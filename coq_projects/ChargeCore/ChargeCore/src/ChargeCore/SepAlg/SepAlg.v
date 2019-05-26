Require Import Setoid Morphisms RelationClasses Program.Basics Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section SepAlgSect.
  Class SepAlgOps T:= {
    sa_unit : T -> Prop;
    sa_mul : T -> T -> T -> Prop
  }.

  Class SepAlg T `{rel : T -> T -> Prop} `{SAOps: SepAlgOps T} : Type := {
    sa_type            :> Equivalence rel;
    sa_mulC a b c      : sa_mul a b c -> sa_mul b a c;
    sa_mulA a b c      : forall ab abc, sa_mul a b ab -> sa_mul ab c abc ->
                                        exists bc, sa_mul b c bc /\ sa_mul a bc abc;
    sa_unit_ex a       : exists e, sa_unit e /\ sa_mul a e a;
    sa_unit_eq a a' e  : sa_unit e -> sa_mul a e a' -> rel a' a;
    sa_unit_proper     : Proper (rel ==> iff) sa_unit;
    sa_mul_mon a b c d : rel a b -> sa_mul a c d -> sa_mul b c d
  }.

End SepAlgSect.

Arguments SepAlg {T} {rel} {SAOps} : rename.

Section SepAlgCompat.
  Context A `{SA: SepAlg A}.

  Definition compat (a b : A) := exists s, sa_mul a b s.
  Definition subheap (a b : A) := exists c, sa_mul a c b.

  Lemma sa_mul_monR (a b c d : A) (Habc : sa_mul a b c) (Hcd: rel c d) : sa_mul a b d.
  Proof.
  	pose proof (sa_unit_ex d) as [u [H1 H2]].
  	apply symmetry in Hcd.
  	apply (sa_mul_mon Hcd) in H2.
  	pose proof @sa_mulA as H3.
  	specialize (H3 _ _ _ _ _ _ _ _ _ Habc H2).
  	destruct H3 as [ac [H3 H4]].
  	apply (sa_unit_eq H1) in H3.
  	apply sa_mulC. eapply sa_mul_mon; [| eapply sa_mulC]; eassumption.
  Qed.

  Lemma sa_mulC2 a b c : sa_mul a b c <-> sa_mul b a c.
  Proof.
    split; apply sa_mulC.
  Qed.

  Global Instance sa_mul_proper : Proper (rel ==> rel ==> rel ==> iff) sa_mul.
  Proof.
  	intros a b Hab c d Hcd f g Hfg; split; intros H.
  	+ eapply sa_mul_mon; [eassumption|].
  	  eapply sa_mulC; eapply sa_mul_mon; [eassumption|]; eapply sa_mulC.
  	  eapply sa_mul_monR; eassumption.
  	+ eapply sa_mul_mon; [symmetry; eassumption|].
  	  eapply sa_mulC; eapply sa_mul_mon; [symmetry; eassumption|]; eapply sa_mulC.
  	  eapply sa_mul_monR; [|symmetry]; eassumption.
  Qed.

End SepAlgCompat.

Module SepAlgNotations.
  Notation "a '-' b" := (sa_mul a b) (at level 50, left associativity) : sa_scope.
  Notation "a '-' b |-> c" := (sa_mul a b c) (at level 52, no associativity) : sa_scope.
  Notation "^" := sa_unit : sa_scope.
  Notation "a # b" := (compat a b) (at level 70, no associativity) : sa_scope.
  Notation "a <= b" := (subheap a b) (at level 70, no associativity) : sa_scope.
End SepAlgNotations.

Import SepAlgNotations.

Delimit Scope sa_scope with sa.

Instance subheap_preo A `{sa : SepAlg A} : PreOrder (@subheap A SAOps).
Proof.
  split.
  + intros a. pose proof (sa_unit_ex a) as [u [H1 H2]].
    unfold subheap. exists u. apply H2.
  + intros a ab abc Hab Habc.
    destruct Hab as [b Hab].
    destruct Habc as [c Habc].
    pose proof (sa_mulA Hab Habc) as [bc [H1 H2]].
    exists bc. apply H2.
Qed.

Instance compat_symm A `{sa : SepAlg A} : Symmetric (compat (A := A)).
Proof.
	intros a b [ab Hab].
	exists ab. apply sa_mulC. apply Hab.
Qed.

Existing Instance sa_unit_proper.

(* From MSL: Two units are equal if they are units of two elements
   related by the extension order. *)
Lemma join_sub_units_eq A `{SepAlg A} (a b ea eb a': A):
  sa_mul a a' b ->
  sa_mul a ea a -> sa_unit ea ->
  sa_mul b eb b -> sa_unit eb ->
  rel ea eb.
Proof.
  intros Hab Hmulea Hunitea Hmuleb Huniteb.
  apply sa_mulC in Hmulea.
  destruct (sa_mulA Hmulea Hab) as [b' [_ Hb']].
  apply sa_mulC in Hb'.
  destruct (sa_mulA Hb' Hmuleb) as [eab [Heab _]].
  transitivity eab.
  - symmetry. eauto using sa_unit_eq.
  - apply sa_mulC in Heab. eauto using sa_unit_eq.
Qed.

Section Properties.
  Context A `{sa : SepAlg A}.
  Open Scope sa_scope.

  Global Instance sa_subheap_equiv_proper :
    Proper (rel ==> rel ==> iff) (subheap (A := A)).
  Proof.
    intros x y Heqxy t u Heqtu; split; intros [c H]; exists c;
    [rewrite <- Heqxy; rewrite <- Heqtu | rewrite  Heqxy; rewrite Heqtu]; assumption.
  Qed.

  Global Instance sa_subheap_subheap_proper :
     Proper (subheap --> subheap ++> impl) (subheap (A := A)).
  Proof.
	intros x y [a Hyax] t u [b Hubt] [c Hxct].
	destruct (sa_mulA Hyax Hxct) as [d [_ Hydt]].
	destruct (sa_mulA Hydt Hubt) as [f [_ Hyfu]].
	exists f. apply Hyfu.
  Qed.

  Global Instance sa_compat_equiv_proper :
    Proper (rel ==> rel ==> iff) (compat (A := A)).
  Proof.
    intros x y Heqxy t u Heqtu; split; [intros [s Heqxst] | intros [s Heqysu]]; exists s.
    + rewrite <- Heqxy, <- Heqtu; assumption.
    + rewrite Heqxy, Heqtu; assumption.
  Qed.

  Lemma compat_subheap {r t : A} (s : A) (Hsr: r <= s) (Hst: s # t) : r # t.
  Proof.
    destruct Hsr as [sr Hsr]; destruct Hst as [st Hst].
    apply sa_mulC in Hsr.
    destruct (sa_mulA Hsr Hst) as [u [Hst2 Hu]].
    exists u. assumption.
  Qed.

  Lemma subheapT (a b c : A) (Hab: a <= b) (Hbc: b <= c) : a <= c.
  Proof.
    unfold subheap in *.
    destruct Hab as [f Hadb].
    destruct Hbc as [g Hbfc].
    destruct (sa_mulA Hadb Hbfc) as [ac [_ H]].
    exists ac. apply H.
  Qed.

 Close Scope sa_scope.

End Properties.

Arguments SepAlg _ {rel SAOps} : rename.
Arguments subheap {A} {SAOps}.
Arguments subheapT {A rel SAOps SA} [_ _ _] : rename.
Arguments compat_subheap {A rel SAOps SA} [_ _ _] _ _ : rename.
