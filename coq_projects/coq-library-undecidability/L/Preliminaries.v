(** * Preliminaries *)

(* Switch Coq into implicit argument mode *)

Global Set Implicit Arguments. 
Global Unset Strict Implicit.

(* Load basic Coq libraries *)

Require Export Omega List Morphisms.

(* Inversion tactic *)

Ltac inv H := inversion H; subst; clear H.

(* Beteva destuct tactics *)

Tactic Notation "destruct" "_":=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X 
  end.

Tactic Notation "destruct" "_" "eqn" ":" ident(E)   :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:E
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X eqn:E
  end.

Tactic Notation "destruct" "_" "eqn" ":" "_"   :=
  let E := fresh "E" in
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:E
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X eqn:E
  end.

Tactic Notation "destruct" "*" :=
  repeat destruct _.

Tactic Notation "destruct" "*" "eqn" ":" ident(E) :=
  repeat (let E := fresh E in destruct _ eqn:E; try progress inv E); try now congruence.

Tactic Notation "destruct" "*" "eqn" ":" "_" := destruct * eqn:E.

(* ** Decidability *)

Definition dec (X : Prop) : Type := {X} + {~ X}.

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

(* Register dec as a type class *)

Existing Class dec.

Definition decision (X : Prop) (D : dec X) : dec X := D.
Arguments decision X {D}.

Tactic Notation "decide" constr(p) := 
  destruct (decision p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (decision p) as i.

(* Hints for auto concerning dec *)

Hint Unfold dec.
Hint Extern 4 =>     
match goal with
  | [  |- dec ?p ] => exact (decision p)
end.

(* Improves type class inference *)

Hint Extern 4 =>     
match goal with
  | [  |- dec ((fun _ => _) _) ] => simpl
end : typeclass_instances.

(* Regiseva instance rules for dec *)

Instance True_dec :  dec True := 
  left I.

Instance False_dec :  dec False := 
  right (fun A => A).

Instance impl_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X -> Y).
Proof.
  unfold dec; tauto. 
Defined.

Instance and_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X /\ Y).
Proof. 
  unfold dec; tauto. 
Defined.

Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof. 
  unfold dec; tauto. 
Defined.

(* Coq standard modules make "not" and "iff" opaque for type class inference, can be seen with Print HintDb typeclass_instances. *)

Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof. 
  unfold not. auto.
Defined.

Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof. 
  unfold iff. auto.
Qed.

Lemma dec_DN X : 
  dec X -> ~~ X -> X.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_and X Y :  
  dec X -> dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_impl X Y :  
  dec X -> dec Y -> ~ (X -> Y) -> X /\ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_prop_iff (X Y : Prop) : 
  (X <-> Y) -> dec X -> dec Y.
Proof.
  unfold dec; tauto.
Defined.

Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  intros x y. hnf. decide equality.
Defined.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  intros x y. hnf. decide equality.
Defined.

Instance prod_eq_dec X Y : eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  intros ? ? ? ?. hnf. decide equality. eapply X1. eapply X0.
Defined.

Instance nat_le_dec (x y : nat) : dec (x <= y) := 
  le_dec x y.

(* * Lists *)

(* Notations for lists *)

Definition equi X (A B : list X) : Prop :=
  incl A B /\ incl B A.

Hint Unfold equi.

Export ListNotations.
Notation "| A |" := (length A) (at level 65).
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "A === B" := (equi A B) (at level 70).

(* The following comments are for coqdoc *)
(** printing el ∊ *)
(** printing <<= ⊆ *)
(** printing === ≡ *)

(* A useful lemma *)

Lemma list_cycle  (X : Type) (A : list X) x :
  x::A <> A.
Proof.
  intros B.
  assert (C: |x::A| <> |A|) by (simpl; omega).
  apply C. now rewrite B.
Qed.

(* Decidability laws for lists *)

Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  intros D. apply list_eq_dec. exact D. 
Defined.

Instance list_in_dec (X : Type) (x : X) (A : list X) :  
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Defined.

Lemma list_sigma_forall X A (p : X -> Prop) (p_dec : forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  induction A as [|x A]; simpl.
  - tauto.
  - destruct IHA as [[y [D E]]|D].
    + eauto. 
    + destruct (p_dec x) as [E|E].
      * eauto.
      * right. intros y [[]|F]; auto. 
Defined.

Arguments list_sigma_forall {X} A p {p_dec}.

Instance list_forall_dec X A (p : X -> Prop) (p_dec : forall x, dec (p x)) :
  dec (forall x, x el A -> p x).
Proof.
  destruct (list_sigma_forall A (fun x => ~ p x)) as [[x [D E]]|D].
  - right. auto.
  - left. intros x E. apply dec_DN; auto.
Defined.

Instance list_exists_dec X A (p : X -> Prop) (p_dec : forall x, dec (p x)) :
  dec (exists x, x el A /\ p x).
Proof.
  destruct (list_sigma_forall A p) as [[x [D E]]|D].
  - eauto.
  - right. intros [x [E F]]. exact (D x E F).
Defined.

Lemma list_exists_DM X A  (p : X -> Prop) : 
  (forall x, dec (p x)) ->
  ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof. 
  intros D E. 
  destruct (list_sigma_forall A p) as [F|F].
  + destruct F as [x F]. eauto.
  + contradiction (E F).
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, dec (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (list_sigma_forall A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Defined.

(* Membership

We use the following facts from the standard library List.
- [in_eq :  x el x::A]
- [in_nil :  ~ x el nil]
- [in_cons :  x el A -> x el y::A]
- [in_or_app :  x el A \/ x el B -> x el A++B]
- [in_app_iff :  x el A++B <-> x el A \/ x el B]
- [in_map_iff :  y el map f A <-> exists x, f x = y /\ x el A]
*)

Hint Resolve in_eq in_nil in_cons in_or_app.

Lemma in_sing X (x y : X) :
  x el [y] -> x = y.

Proof. simpl. intros [[]|[]]. reflexivity. Qed.

Lemma in_cons_neq X (x y : X) A :
  x el y::A -> x <> y -> x el A.

Proof. simpl. intros [[]|D] E; congruence. Qed.

(* Inclusion
-
-We use the following facts from the standard library List.
-- [A <<= B = forall y, x el A -> x el B]
-- [incl_refl :  A <<= A]
-- [incl_tl :  A <<= B -> A <<= x::B]
-- [incl_cons : x el B -> A <<= B -> x::A <<= B]
-- [incl_appl : A <<= B -> A <<= B++C]
-- [incl_appr : A <<= C -> A <<= B++C]
-- [incl_app : A <<= C -> B <<= C -> A++B <<= C]
-*)

Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app.

Lemma incl_nil X (A : list X) :
  nil <<= A.

Proof. intros x []. Qed.

Hint Resolve incl_nil.

Lemma incl_map X Y A B (f : X -> Y) :
  A <<= B -> map f A <<= map f B.

Proof.
  intros D y E. apply in_map_iff in E as [x [E E']].
  subst y. apply in_map_iff. eauto.
Qed.

Section Inclusion.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma incl_nil_eq A :
    A <<= nil -> A=nil.

  Proof.
    intros D. destruct A as [|x A].
    - reflexivity.
    - exfalso. apply (D x). auto.
  Qed.

  Lemma incl_shift x A B :
    A <<= B -> x::A <<= x::B.

  Proof. intros D y E. destruct E; subst; auto. Qed.

  Lemma incl_lcons x A B :
    x::A <<= B <-> x el B /\ A <<= B.

  Proof. 
    split. 
    - intros D. split; hnf; auto.
    - intros [D E] z [F|F]; subst; auto.
  Qed.

  Lemma incl_rcons x A B :
    A <<= x::B -> ~ x el A -> A <<= B.

  Proof. intros C D y E. destruct (C y E) as [F|F]; congruence. Qed.

  Lemma incl_lrcons x A B :
    x::A <<= x::B -> ~ x el A -> A <<= B.

  Proof.
    intros C D y E.
    assert (F: y el x::B) by auto.
    destruct F as [F|F]; congruence.
  Qed.

End Inclusion.

Hint Resolve incl_shift.

Definition inclp (X : Type) (A : list X) (p : X -> Prop) : Prop :=
  forall x, x el A -> p x.

(* Setoid rewriting with list inclusion and list equivalence *)

Instance in_equi_proper X : 
  Proper (eq ==> @equi X ==> iff) (@In X).

Proof. hnf. intros x y []. hnf. firstorder. Qed.

Instance incl_equi_proper X : 
  Proper (@equi X ==> @equi X ==> iff) (@incl X).

Proof. hnf. intros x y D. hnf. firstorder. Qed.

Instance incl_preorder X : PreOrder (@incl X).

Proof. constructor; hnf; unfold incl; auto. Qed.

Instance equi_Equivalence X : Equivalence (@equi X).

Proof. constructor; hnf; firstorder. Qed.

Instance cons_equi_proper X : 
  Proper (eq ==> @equi X ==> @equi X) (@cons X).

Proof. hnf. intros x y []. hnf. firstorder. Qed.

Instance app_equi_proper X : 
  Proper (@equi X ==> @equi X ==> @equi X) (@app X).

Proof. 
  hnf. intros A B D. hnf. intros A' B' E.
  destruct D, E; auto.
Qed.

(* Equivalence *)

Section Equi.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma equi_push x A :
    x el A -> A === x::A.

  Proof. auto. Qed.

  Lemma equi_dup x A :
    x::A === x::x::A.

  Proof. auto. Qed.

  Lemma equi_swap x y A:
    x::y::A === y::x::A.

  Proof. split; intros z; simpl; tauto. Qed.

  Lemma equi_shift x A B :
    x::A++B === A++x::B.

  Proof. 
    split; intros y.
    - intros [D|D].
      + subst; auto.
      + apply in_app_iff in D as [D|D]; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + destruct D; subst; auto.
  Qed.

  Lemma equi_rotate x A :
    x::A === A++[x].
  
  Proof. 
    split; intros y; simpl.
    - intros [D|D]; subst; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + apply in_sing in D. auto.
  Qed.
End Equi.

(* * Filter *)

Definition filter (X : Type) (p : X -> Prop) (p_dec : forall x, dec (p x)) : list X -> list X :=
  fix f A := match A with
              | nil => nil
              | x::A' => if decision (p x) then x :: f A' else f A'
            end.

Arguments filter {X} p {p_dec} A.

Section FilterLemmas.
  Variable X : Type.
  Variable p : X -> Prop.
  Context {p_dec : forall x, dec (p x)}.

  Lemma in_filter_iff x A :
    x el filter p A <-> x el A /\ p x.
    
  Proof. 
    induction A as [|y A]; simpl.
    - tauto.
    - decide (p y) as [B|B]; simpl;
      rewrite IHA; intuition; subst; tauto.
  Qed.

  Lemma filter_incl A :
    filter p A <<= A.
  
  Proof.
    intros x D. apply in_filter_iff in D. apply D.
  Qed.

  Lemma filter_mono A B :
    A <<= B -> filter p A <<= filter p B.

  Proof.
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_fst x A :
    p x -> filter p (x::A) = x::filter p A.
  Proof.
    simpl. decide (p x); tauto.
  Qed.

  Lemma filter_app A B :
    filter p (A ++ B) = filter p A ++ filter p B.
  Proof.
    induction A as [|y A]; simpl.
    - reflexivity.
    - rewrite IHA. decide (p y); reflexivity.  
  Qed.

  Lemma filter_fst' x A :
    ~ p x -> filter p (x::A) = filter p A.
  Proof.
    simpl. decide (p x); tauto.
  Qed.

End FilterLemmas.

(* * Element removal *)

Section Removal.
  Variable X : Type.
  Context {eq_X_dec : eq_dec X}.

  Definition rem (A : list X) (x : X) : list X :=
    filter (fun z => z <> x) A.

  Lemma in_rem_iff x A y :
    x el rem A y <-> x el A /\ x <> y.
  Proof.
    apply in_filter_iff.
  Qed.

  Lemma rem_not_in x y A :
    x = y \/ ~ x el A -> ~ x el rem A y.
  Proof.
    intros D E. apply in_rem_iff in E. tauto.
  Qed.

  Lemma rem_incl A x :
    rem A x <<= A.
  Proof.
    apply filter_incl.
  Qed.

  Lemma rem_mono A B x :
    A <<= B -> rem A x <<= rem B x.
  Proof.
    apply filter_mono.
  Qed.

  Lemma rem_cons A B x :
    A <<= B -> rem (x::A) x <<= B.
  Proof.
    intros E y F. apply E. apply in_rem_iff in F.
    destruct F as [[|]]; congruence.
  Qed.

  Lemma rem_cons' A B x y :
    x el B -> rem A y <<= B -> rem (x::A) y <<= B.
  Proof.
    intros E F u G. 
    apply in_rem_iff in G as [[[]|G] H]. exact E.
    apply F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_in x y A :
    x el rem A y -> x el A.
  Proof.
    apply rem_incl.
  Qed.

  Lemma rem_neq x y A :
    x <> y -> x el A -> x el rem A y.
  Proof.
    intros E F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_app x A B :
    x el A -> B <<= A ++ rem B x.
  Proof.
    intros E y F. decide (x=y) as [[]|]; auto using rem_neq.
  Qed.

  Lemma rem_equi x A :
    x::A === x::rem A x.
  Proof.
    split; intros y; 
    intros [[]|E]; decide (x=y) as [[]|D]; 
    eauto using rem_in, rem_neq. 
  Qed.

  Lemma rem_fst x A :
    rem (x::A) x = rem A x.
  Proof.
    unfold rem. rewrite filter_fst'; auto.
  Qed.

  Lemma rem_fst' x y A :
    x <> y -> rem (x::A) y = x::rem A y.
  Proof.
    intros E. unfold rem. rewrite filter_fst; auto.
  Qed.

End Removal.

Hint Resolve rem_not_in rem_incl rem_mono rem_cons rem_cons' rem_app rem_in rem_neq.

(* * Duplicate-free lists *)

Inductive dupfree (X : Type) : list X -> Prop :=
| dupfreeN : dupfree nil
| dupfreeC x A : ~ x el A -> dupfree A -> dupfree (x::A).

Section Dupfree.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma dupfree_inv x A :
    dupfree (x::A) <-> ~ x el A /\ dupfree A.
  Proof. 
    split; intros D.
    - inv D; auto.
    - apply dupfreeC; tauto.
  Qed.

  Lemma dupfree_map Y A (f : X -> Y) :
    (forall x y, x el A -> y el A -> f x = f y -> x=y) -> 
    dupfree A -> dupfree (map f A).

  Proof.
    intros D E. induction E as [|x A E' E]; simpl.
    - constructor.
    - constructor; [|now auto].
      intros F. apply in_map_iff in F as [y [F F']].
      rewrite (D y x) in F'; auto.
  Qed.

  Lemma dupfree_filter p (p_dec : forall x, dec (p x)) A :
    dupfree A -> dupfree (filter p A).

  Proof.
    intros D. induction D as [|x A C D]; simpl.
    - left.
    - decide (p x) as [E|E]; [|exact IHD].
      right; [|exact IHD].
      intros F. apply C. apply filter_incl in F. exact F.
   Qed.

  Lemma dupfree_dec A :
    eq_dec X -> dec (dupfree A).

  Proof.
    intros D. induction A as [|x A].
    - left. left.
    - decide (x el A) as [E|E].
      + right. intros F. inv F; tauto.
      + destruct (IHA) as [F|F].
        * auto using dupfree.
        * right. intros G. inv G; tauto.
  Qed.

End Dupfree.

Section Undup.
  Variable X : Type.
  Context {eq_X_dec : eq_dec X}.
  Implicit Types A B : list X.

  Fixpoint undup (A : list X) : list X :=
    match A with
      | nil => nil
      | x::A' => if decision (x el A') then undup A' else  x :: undup A'
    end.

  Lemma undup_fp_equi A :
    undup A === A.
  Proof.
    induction A as [|x A]; simpl.
    - reflexivity.
    - decide (x el A) as [E|E]; rewrite IHA; auto.
  Qed.

  Lemma dupfree_undup A :
    dupfree (undup A).
  Proof.
    induction A as [|x A]; simpl.
    - left.
    - decide (x el A) as [E|E]; auto.
      right; auto. now rewrite undup_fp_equi. 
  Qed.

  Lemma undup_incl A B :
    A <<= B <-> undup A <<= undup B.
  Proof.
    now do 2 rewrite undup_fp_equi.
  Qed.

  Lemma undup_equi A B :
    A === B <-> undup A === undup B.
  Proof.
    now do 2 rewrite undup_fp_equi.
  Qed.

  Lemma undup_eq A :
    dupfree A -> undup A = A.
  Proof.
    intros E. induction E as [|x A E F]; simpl.
    - reflexivity.
    - rewrite IHF. decide (x el A) as [G|G]; tauto.
  Qed.

  Lemma undup_idempotent A :
    undup (undup A) = undup A.

  Proof. apply undup_eq, dupfree_undup. Qed.

End Undup.

Section DupfreeLength.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma dupfree_reorder A x :
    dupfree A -> x el A -> 
    exists A', A === x::A' /\ |A'| < |A| /\ dupfree (x::A').

  Proof.
    intros E. revert x. induction E as [|y A H]; intros x F.
    - contradiction F.
    - destruct F as [F|F].
      + subst y. exists A. auto using dupfree. 
      + specialize (IHE x F). destruct IHE as [A' [G [K1 K2]]].
        exists (y::A'). split; [|split].
        * rewrite G. apply equi_swap.
        * simpl. omega.
        * { apply dupfree_inv in K2 as [K2 K3]. right. 
            - intros [M|M]; subst; auto.
            - right; [|exact K3].
              intros M; apply H. apply G. auto. }
   Qed.

  Lemma dupfree_le A B :
    dupfree A -> dupfree B -> A <<= B -> |A| <= |B|.

  Proof. 
    intros E; revert B.
    induction A as [|x A]; simpl; intros B F G.
    - omega.
    - apply incl_lcons in G as [G H]. 
      destruct (dupfree_reorder F G) as [B' [K [L M]]].
      apply dupfree_inv in E as [E1 E2].
      apply dupfree_inv in M as [M1 M2].
      cut (A <<= B').
      { intros N. specialize (IHA E2 B' M2 N). omega. }
      apply incl_rcons with (x:=x); [|exact E1].
      rewrite H. apply K.
  Qed.

  Lemma dupfree_eq A B :
    dupfree A -> dupfree B -> A === B -> |A|=|B|.

  Proof. 
    intros D E [F G]. 
    apply (dupfree_le D E) in F. 
    apply (dupfree_le E D) in G. 
    omega.
  Qed.

  Lemma dupfree_lt A B x :
    dupfree A -> dupfree B -> A <<= B -> 
    x el B -> ~ x el A  -> |A| < |B|.

  Proof.
    intros E F G H K.
    destruct (dupfree_reorder F H) as [B' [L [M N]]].
    rewrite (dupfree_eq F N L). 
    cut (|A|<=|B'|). { simpl; omega. }
    apply dupfree_le.
    - exact E.
    - now inv N.
    - apply incl_rcons with (x:=x).
      + rewrite G. apply  L.
      + exact K.
  Qed.

  Lemma dupfree_ex A B :
    eq_dec X -> dupfree A -> dupfree B -> |A| < |B| -> exists x, x el B /\ ~ x el A.

  Proof.
    intros D E F H.
    destruct (list_sigma_forall B (fun x => ~ x el A)) as [[x K]|K].
    - exists x; exact K.
    - exfalso. 
      assert (L : B <<= A).
      { intros x L. apply dec_DN; auto. }
      apply dupfree_le in L; auto; omega.
  Qed.

  Lemma dupfree_equi A B :
    eq_dec X -> dupfree A -> dupfree B -> A <<= B -> |A|=|B| -> A === B.

  Proof.
    intros C D E F G. split. exact F.
    destruct (list_sigma_forall B (fun x => ~ x el A)) as [[x [H K]]|H].
    - exfalso. assert (L:=dupfree_lt D E F H K). omega.
    - intros x L. apply dec_DN; auto.
  Qed.

End DupfreeLength.
 
(* * Cardinality *)

Section Cardinality.
  Variable X : Type.
  Context {eq_X_dec : eq_dec X}.
  Implicit Types A B : list X.

  Definition card (A : list X) : nat := |undup A|.

  Lemma card_le A B :
    A <<= B -> card A <= card B.

  Proof.
    intros E. apply dupfree_le.
    - apply dupfree_undup. 
    - apply dupfree_undup.
    - apply undup_incl, E.
  Qed.

  Lemma card_eq A B :
    A === B -> card A = card B.

  Proof.
    intros [E F]. apply card_le in E. apply card_le in F. omega.
  Qed.

  Lemma card_equi A B :
    A <<= B -> card A = card B -> A === B.
  Proof.
    intros D E.
    apply <- undup_equi. apply -> undup_incl in D.
    apply dupfree_equi; auto using dupfree_undup.    
  Qed.

  Lemma card_lt A B x :
    A <<= B -> x el B -> ~ x el A -> card A < card B.

  Proof.
    intros D E F.
    apply (dupfree_lt (A:= undup A) (B:= undup B) (x:=x)).
    - apply dupfree_undup.
    - apply dupfree_undup.
    - apply undup_incl, D.
    - apply undup_fp_equi, E.
    - rewrite undup_fp_equi. exact F.
  Qed.

  Lemma card_or A B :
    A <<= B -> A === B \/ card A < card B.

  Proof.
    intros D.
    decide (card A = card B) as [F|F].
    - left. apply card_equi; auto.
    - right. apply card_le in D. omega.
  Qed.

  Lemma card_ex A B :
    card A < card B -> exists x, x el B /\ ~ x el A.

  Proof.
    intros E.
    destruct (dupfree_ex (A:=undup A) (B:=undup B)) as [x F].
    - exact eq_X_dec.
    - apply dupfree_undup.
    - apply dupfree_undup.
    - exact E.
    - exists x. setoid_rewrite undup_fp_equi in F. exact F.
     (*Coq bug: Must use setoid_rewrite here *)
  Qed.

  Lemma card_cons x A :
    card (x::A) = if decision (x el A) then card A else 1 + card A.
  Proof.
    unfold card at 1; simpl. now decide (x el A). 
  Qed.

  Lemma card_cons_rem x A :
    card (x::A) = 1 + card (rem A x).
  Proof.
    rewrite (card_eq (rem_equi x A)). 
    rewrite card_cons.
    decide (x el rem A x) as [D|D].
    - apply in_rem_iff in D; tauto.
    - reflexivity.
  Qed.

  Lemma card_0 A :
    card A = 0 -> A = nil.
  Proof.
    destruct A as [|x A]; intros D.
    - reflexivity.
    - exfalso. rewrite card_cons_rem in D. omega.
  Qed.

End Cardinality.

Instance card_equi_proper X (D: eq_dec X) : 
  Proper (@equi X ==> eq) (@card X D).
Proof. 
  hnf. apply card_eq.
Qed.

Lemma complete_induction (p : nat -> Prop) (x : nat) :
(forall x, (forall y, y<x -> p y) -> p x) -> p x.

Proof. intros A. apply A. induction x ; intros y B.
exfalso ; omega.
apply A. intros z C. apply IHx. omega. Qed.

Lemma size_induction X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> 
  forall x, p x.

Proof. 
  intros IH x. apply IH. 
  assert (G: forall n y, f y < n -> p y).
  { intros n. induction n.
    - intros y B. exfalso. omega.
    - intros y B. apply IH. intros z C. apply IHn. omega. }
  apply G.
Qed.

(** Positions and map-products for lists *)

Section Positions.
  Variables (X: Type) (d: eq_dec X).
  Implicit Types (x y: X) (A B : list X).

  Fixpoint pos x A : option nat :=
    match A with
    | nil => None
    | y :: A' => if d x y then Some 0
                else match pos x A' with
                     | Some n => Some (S n)
                     | None => None
                     end
    end.

  Lemma el_pos x A :
    x el A -> { n | pos x A = Some n }.
  Proof.
    induction A as [|y A IH]; cbn; intros H.
    - destruct H as [].
    - destruct (d x y) as [<-|H1].
      + now exists 0.
      + destruct IH as [n IH].
        * destruct H as [->|H]; tauto.
        * rewrite IH. now exists (S n).
  Qed.

  Fixpoint nth n A : option X :=
    match A, n with
    | nil, _ => None
    | x::_, 0 => Some x
    | _::A', S n' => nth n' A'
    end.

  Lemma nth_length A n :
    length A > n -> { x | nth n A = Some x }.
  Proof.
    revert n.
    induction A as [|y A IH]; cbn; intros n H.
    - exfalso. omega.
    - destruct n as [|n]; cbn.
      + now exists y.
      + destruct (IH n) as [x H1]. omega. now exists x.
  Qed.
  
 Lemma pos_nth x A n :
    pos x A = Some n -> nth n A = Some x.
 Proof.
   revert n.
   induction A as [|y A IH]; cbn; intros n.
    - intros [=].
    - destruct (d x y) as [<-|H1].
      + now intros [= <-].
      + destruct (pos x A) as [k|]; intros [= <-]; cbn.
        now apply IH.
  Qed.
  
  Lemma nth_app_l x n A B :
    nth n A = Some x -> nth n (A ++ B) = Some x.
  Proof.
    revert n.
    induction A as [|y A IH]; cbn; intros k H.
    - destruct k; discriminate H.
    - destruct k as [|k]; cbn in *. exact H.
      apply IH, H.
  Qed.

End Positions.

Section MapProduct.
  Variables (X Y Z: Type) (f: X -> Y -> Z).

  Fixpoint map_pro (A: list X) (B: list Y) : list Z :=
    match A with
    | x :: A' => map_pro A' B ++ map (f x) B
    | nil => nil
    end.

  Lemma map_pro_in x A B :
    x el map_pro A B <-> exists a b, a el A /\ b el B /\ f a b = x.
  Proof.
  induction A as [|a A IH]; cbn.
  - firstorder.
  - rewrite in_app_iff, IH, in_map_iff. 
    firstorder; subst; eauto.
  Qed.

End MapProduct.


(* Section pos. *)
  
(*   Definition elAt := nth_error. *)
(*   Notation "A '.[' i  ']'" := (elAt A i) (no associativity, at level 50). *)
  
(*   Fixpoint pos (X : Type) {e : eq_dec X} (s : X) (A : list X) := *)
(*     match A with *)
(*       | nil => None *)
(*       | a :: A => if decision (s = a) then Some 0 else match pos s A with None => None | Some n => Some (S n) end *)
(*     end. *)
  
(*   Lemma el_pos X (E : eq_dec X) s A : s el A -> exists m, pos s A = Some m. *)
(*   Proof. *)
(*     revert s; induction A; simpl; intros s H. *)
(*       - contradiction. *)
(*       - decide (s = a) as [D | D]; eauto;  *)
(*         destruct H; try congruence. *)
(*         destruct (IHA s H) as [n Hn]; eexists; now rewrite Hn. *)
(*   Qed. *)
  
(*   Lemma pos_elAt X (_ : eq_dec X) s A i : pos s A = Some i -> A .[i] = Some s. *)
(*   Proof. *)
(*     revert i s. induction A; intros i s. *)
(*     - destruct i; inversion 1. *)
(*     - simpl. decide (s = a). *)
(*       + inversion 1; subst; reflexivity. *)
(*       + destruct i; destruct (pos s A) eqn:B; inversion 1; subst; eauto.  *)
(*   Qed. *)
  
(*   Lemma elAt_app X (A : list X) i B s : A .[i] = Some s -> (A ++ B).[i] = Some s. *)
(*   Proof. *)
(*     revert s B i. induction A; intros s B i H; destruct i; simpl; intuition; inv H. *)
(*   Qed. *)
  
(*   Lemma elAt_el (X : Type) A (s : X) m : A .[ m ] = Some s -> s el A. *)
(*   Proof. *)
(*     revert A. induction m; intros []; inversion 1; eauto. *)
(*   Qed. *)
  
(*   Lemma el_elAt X {_ : eq_dec X} (s : X) A : s el A -> exists m, A .[ m ] = Some s. *)
(*   Proof. *)
(*     intros H; destruct (el_pos _ H); eexists; eauto using pos_elAt. *)
(*   Qed. *)

(* Lemma dupfree_elAt X (A : list X) n m s : dupfree A -> A.[n] = Some s -> A.[m] = Some s -> n = m. *)
(* Proof with try tauto. *)
(*   intros H; revert n m; induction A; simpl; intros n m H1 H2. *)
(*   - destruct n; inv H1. *)
(*   - destruct n, m; inv H... *)
(*     + inv H1. simpl in H2. eapply elAt_el in H2... *)
(*     + inv H2. simpl in H1. eapply elAt_el in H1...  *)
(*     + inv H1. inv H2. rewrite IHA with n m...  *)
(* Qed. *)

(* Lemma nth_error_none A n l : nth_error l n = @None A -> length l <= n. *)
(* Proof. revert n; *)
(*   induction l; intros n. *)
(*   - simpl; omega. *)
(*   - simpl. intros. destruct n. inv H. inv H. assert (| l | <= n). eauto. omega. *)
(* Qed. *)

(* End pos. *)
