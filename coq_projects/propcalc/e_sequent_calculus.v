Require Export c_completeness.
Set Implicit Arguments.

Module Type sequent_mod (B: base_mod) (S: sound_mod B) (C: complete_mod B S).
Import B S C.

(** * Gentzen's Sequent Calculus *)

Reserved Notation "Γ ⊃ A" (at level 80).
Inductive G : list PropF->list PropF->Prop :=
| Gax  : forall A Γ Δ      , In A Γ           -> In A Δ          -> Γ ⊃ Δ
| GBot : forall Γ Δ        , In ⊥ Γ                              -> Γ ⊃ Δ
| AndL : forall A B Γ1 Γ2 Δ, Γ1++A::B::Γ2 ⊃ Δ                    -> Γ1++A∧B::Γ2 ⊃ Δ
| AndR : forall A B Γ Δ1 Δ2, Γ ⊃ Δ1++A::Δ2    -> Γ ⊃ Δ1++B::Δ2   -> Γ ⊃ Δ1++A∧B::Δ2
| OrL  : forall A B Γ1 Γ2 Δ, Γ1++A::Γ2 ⊃ Δ    -> Γ1++B::Γ2 ⊃ Δ   -> Γ1++A∨B::Γ2 ⊃ Δ
| OrR  : forall A B Γ Δ1 Δ2, Γ ⊃ Δ1++A::B::Δ2                     -> Γ ⊃ Δ1++A∨B::Δ2
| ImpL : forall A B Γ1 Γ2 Δ, Γ1++B::Γ2 ⊃ Δ    -> Γ1++Γ2 ⊃ A::Δ   -> Γ1++A→B::Γ2 ⊃ Δ
| ImpR : forall A B Γ Δ1 Δ2, A::Γ ⊃ Δ1++B::Δ2                     -> Γ ⊃ Δ1++A→B::Δ2
| Cut  : forall A Γ Δ      , Γ ⊃ A::Δ         -> A::Γ ⊃ Δ        -> Γ ⊃ Δ
where "Γ ⊃ Δ" := (G Γ Δ) : My_scope.


(** The disjunction of a list of formulas*)
Definition BigOr := fold_right Disj ⊥.
Notation "⋁ Δ" := (BigOr Δ) (at level 19).
(** Γ ⊢⊢ Δ means that Γ ⊢ A for all A in Δ*)
Definition Ncl Γ := map_fold_right (Nc Γ) and True.
Notation "Γ ⊢⊢ Δ" := (Ncl Γ Δ) (at level 80).
Notation "¬l Γ" := (map Neg Γ) (at level 40).

(** * Theorems *)

(** Gc to Nc*)

Lemma NegAnd_impl_OrNeg : forall Γ A B, Γ ⊢ ¬(A∧B) -> Γ ⊢ ¬A∨¬B.
do 3 intro;apply prov_impl.
apply ImpI;apply BotC;apply ImpE with (A ∧ B);
 [is_ass|apply AndI;apply BotC;(apply ImpE with (¬A ∨ ¬B);[is_ass|])].
   apply OrI1;is_ass.
   apply OrI2;is_ass.
Qed.

Lemma Nc_list_weakening : forall Γ1 Γ2 Δ, (forall B, In B Γ1 -> In B Γ2) -> Γ1 ⊢⊢ Δ -> Γ2 ⊢⊢ Δ.
intros;induction Δ.
 trivial.
 destruct H0;split.
   eapply weakening2;eassumption.
   apply IHΔ;apply H1.
Qed.

Lemma Nc_list_impl : forall Γ A, Γ ⊢ A ->forall Δ, Δ ⊢⊢ Γ -> Δ ⊢ A.
induction 1;intros;[induction Γ;destruct H;[subst;apply H0|apply IHΓ;[assumption|apply H0]]
|constructor 2|econstructor 3|constructor 4|constructor 5|econstructor 6
|econstructor 7|constructor 8|constructor 9|econstructor 10];try eauto;
[apply IHNc..|apply IHNc2|try apply IHNc3];
(split;[is_ass|eapply Nc_list_weakening;[|eassumption];in_solve]).
Qed.

Lemma Nc_list_contained : forall Γ Δ, (forall B, In B Δ -> In B Γ) -> Γ ⊢⊢ Δ.
intros;induction Δ.
 exact I.
 split.
   constructor;apply H;in_solve.
   apply IHΔ;intros;apply H;in_solve.
Qed.

Lemma Nc_list_app : forall Γ Δ1 Δ2, Γ ⊢⊢ Δ1 -> Γ ⊢⊢ Δ2 -> Γ ⊢⊢ Δ1++Δ2.
intros;induction Δ1.
 assumption.
 destruct H;split.
   assumption.
   apply IHΔ1;apply H1.
Qed.

Ltac Ncl_solve := repeat match goal with
| |- _ ⊢ _     => idtac
| |- _ ⊢⊢ _::_ => split;[eassumption||(try (is_ass;fail))|]
| |- _ ⊢⊢ _++_ => apply Nc_list_app
| |- map_fold_right (Nc ?Γ) and True _ => change (map_fold_right (Nc Γ) and True) with (Ncl Γ)
| _            => eassumption||(apply Nc_list_contained;in_solve)
end.

Lemma G_to_Nc_Neg : forall Γ Δ, Γ ⊃ Δ -> Γ++¬l Δ ⊢ ⊥.
induction 1;try rewrite map_app in *;simpl in *.
 mp;[|is_ass]. constructor. apply in_app_iff;right. 
  change (A → ⊥) with (¬A). apply in_map;assumption.
 is_ass.
 eapply Nc_list_impl;[eassumption|]. Ncl_solve.
   eapply AndE1;is_ass.
   eapply AndE2;is_ass.
 eapply OrE;[apply NegAnd_impl_OrNeg;is_ass|eapply Nc_list_impl..];
  [apply IHG1| |apply IHG2|];Ncl_solve.
 eapply OrE;[is_ass|eapply Nc_list_impl..];[apply IHG1| |apply IHG2|];Ncl_solve.
 eapply Nc_list_impl;[eassumption|]. Ncl_solve;(apply ImpI;mp;[is_ass|]).
   eapply OrI1;is_ass.
   eapply OrI2;is_ass.
 eapply OrE;[apply Excluded_Middle|eapply Nc_list_impl..];
  [apply IHG1| |apply IHG2|Ncl_solve];Ncl_solve;mp;is_ass.
 eapply Nc_list_impl;[eassumption|]. Ncl_solve.
   apply BotC;mp;[|apply ImpI;apply BotC;apply ImpE with A];is_ass.
   apply ImpI;mp;[|apply ImpI];is_ass.
 eapply OrE;[apply Excluded_Middle|eapply Nc_list_impl..];
  [apply IHG2| |apply IHG1|];Ncl_solve.
Qed.

Lemma ConjNeg_Disj : forall Δ Γ, Γ ++ ¬l Δ ⊢ ⊥ -> Γ ⊢ ⋁Δ.
induction Δ;simpl;intros.
 rewrite app_nil_r in H;trivial.
 eapply OrE. 
   apply Excluded_Middle.
   apply OrI1;is_ass.
   apply OrI2;apply IHΔ;eapply Nc_list_impl;[eassumption|Ncl_solve].
Qed.

Theorem G_to_Nc : forall Γ Δ, Γ ⊃ Δ -> Γ ⊢ ⋁Δ.
intros;apply ConjNeg_Disj;apply G_to_Nc_Neg;assumption.
Qed.

(** Nc to Gc

The hardest part is proving weakening for Gc*)

Local Ltac temp1 := econstructor;split;reflexivity||(rewrite app_comm_cons;reflexivity).

Lemma in_split_app : forall A (a:A) l2 l4 l1 l3, l1++a::l2=l3++l4 -> ((exists l,l3=l1++a::l/\l2=l++l4)\/
                                                                      (exists l,l4=l++a::l2/\l1=l3++l)).
induction l1;intros;
 (destruct l3;[destruct l4|];discriminate||(injection H;intros;subst)).
   right;exists [];split;reflexivity.
   left;temp1.
   right;temp1.
   destruct (IHl1 _ H0) as [(?&?&?)|(?&?&?)];subst.
     left;temp1.
     right;temp1.
Qed.

Lemma in_in_split_app : forall A (a:A) b l2 l4 l1 l3, l1++a::l2=l3++b::l4 -> (exists l,l3=l1++a::l/\l2=l++b::l4)\/
                                                                            (exists l,l4=l++a::l2/\l1=l3++b::l)\/
                                                                            (a=b/\l1=l3/\l2=l4).
intros;apply in_split_app in H as [(?&?&?)|(?&?&?)];subst.
  left;econstructor;split;reflexivity.
  destruct x;injection H;intros;subst.
    repeat (right||split||rewrite app_nil_r||reflexivity).
    right;left;econstructor;split;reflexivity.
Qed.

Ltac rew1 := repeat rewrite <- app_assoc;repeat rewrite <- app_comm_cons.
Ltac rew2 := repeat rewrite app_comm_cons;try rewrite app_assoc.
Ltac constr := constructor 3||constructor 4||constructor 5||constructor 6||constructor 7||constructor 8.
Local Ltac temp2 X Y Z := 
  (rew1;constr;rew2;eapply X;rew1;reflexivity)||
  (rew2;constr;rew1;eapply X;rew2;reflexivity)||
  (rew1;constr;rew2;[eapply Y|eapply Z];rew1;reflexivity)||
  (rew2;constr;rew1;[eapply Y|eapply Z];rew2;reflexivity).
Local Ltac temp3 H IHG IHG1 IHG2 Heql A0 := induction H;intros;subst;
 try apply in_split_app in Heql as [(?&?&?)|(?&?&?)];
  subst;try (temp2 IHG IHG1 IHG2;fail);[is_ass|constructor 2;in_solve|
   apply Cut with A0;[try rewrite app_comm_cons|rew2];auto..].

Lemma WeakL : forall Γ1 Γ2 Δ A, Γ1++Γ2 ⊃ Δ -> Γ1++A::Γ2 ⊃ Δ.
intros;remember (Γ1++Γ2);revert Γ1 Γ2 Heql;temp3 H IHG IHG1 IHG2 Heql A0.
Qed.

Lemma WeakR : forall Γ Δ1 Δ2 A, Γ ⊃ Δ1++Δ2 -> Γ ⊃ Δ1++A::Δ2.
intros;remember (Δ1++Δ2);revert Δ1 Δ2 Heql;temp3 H IHG IHG1 IHG2 Heql A0.
Qed.

Theorem Nc_to_G : forall Γ A, Γ ⊢ A -> Γ ⊃ [A].
induction 1.
 is_ass.
 apply ImpR with (Δ1:=[]);assumption.
 apply Cut with (A→B).
   apply WeakR with (Δ1:=[_]);assumption.
   apply ImpL with (Γ1:=[]).
     is_ass.
     apply WeakR with (Δ1:=[_]);assumption.
 apply Cut with (¬A).
   apply ImpR with (Δ1:=[]);is_ass.
   eapply Cut.
    apply WeakR with (Δ1:=[⊥]);assumption.
    apply GBot;in_solve.
 apply AndR with (Δ1:=[]);assumption.
 apply Cut with (A ∧ B).
   apply WeakR with (Δ1:=[_]);assumption.
   apply AndL with (Γ1:=[]);is_ass.
 apply Cut with (A ∧ B).
   apply WeakR with (Δ1:=[_]);assumption.
   apply AndL with (Γ1:=[]);constructor 1 with B;in_solve.
 apply OrR with (Δ1:=[]);apply WeakR with (Δ1:=[_]);assumption.
 apply OrR with (Δ1:=[]);apply WeakR;assumption.
 apply Cut with (A ∨ B).
   apply WeakR with (Δ1:=[_]);assumption.
   apply OrL with (Γ1:=[]);assumption.
Qed.

End sequent_mod.