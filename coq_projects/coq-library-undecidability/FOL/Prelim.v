(** * Preliminaries *)

(** This file contains definitions and proofs from the Base Library for the ICL lecture. 
   - Version: 3 October 2016
   - Author: Gert Smolka, Saarland University
   - Acknowlegments: Sigurd Schneider, Dominik Kirst, Yannick Forster
 *)

From Undecidability.L Require Import Tactics.

Require Export Bool Omega List Setoid Morphisms.

Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.
Global Set Regular Subst Tactic.

Hint Extern 4 => exact _.

(** ** Lists *)
Export ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).

Hint Extern 4 => 
match goal with
|[ H: ?x el nil |- _ ] => destruct H
end.

Lemma incl_nil X (A : list X) :
  nil <<= A.
Proof. intros x []. Qed.

Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.
Hint Resolve in_eq in_nil in_cons in_or_app.
Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app incl_nil.

(** ** Tactics *)
Ltac inv H := inversion H; subst; try clear H.

Tactic Notation "destruct" "_":=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X 
  end.

Hint Extern 4 => 
match goal with
|[ H: False |- _ ] => destruct H
|[ H: true=false |- _ ] => discriminate H
|[ H: false=true |- _ ] => discriminate H
end.

Lemma size_induction X (f : X -> nat) (p : X -> Type) :
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


Lemma size_induction_dep L (X : L -> Type) (f : forall l, X l -> nat) (p : forall l, X l -> Type) :
  (forall l x, (forall l' y, f l' y < f l x -> p l' y) -> p l x) -> 
  forall l x, p l x.
Proof. 
  intros IH l x. apply IH. intros l'.
  assert (G: forall n l' y, f l' y < n -> p l' y).
  { intros n. induction n; intros l'' y.
    - intros B. exfalso. omega.
    - intros B. apply IH. intros ll z C. eapply IHn. omega. }
  apply G.
Qed.

(* Definition Injective {A B} (f : A->B) := *)
(*  forall x y, f x = f y -> x = y. *)

(* Section fix_X. *)
(*   Variable X:Type. *)
(*   Implicit Types (A B: list X) (a b c: X).  *)

(*   Lemma last_app_eq A B a b : *)
(*     A++[a] = B++[b] -> A = B /\ a = b. *)
(*   Proof. *)
(*     intros H%(f_equal (@rev X)). rewrite !rev_app_distr in H. split. *)
(*     - inv H. apply (f_equal (@rev X)) in H2. now rewrite !rev_involutive in H2. *)
(*     - now inv H. *)
(*   Qed. *)
  
(*   Lemma rev_eq A B: *)
(*     List.rev A = List.rev B <-> A = B. *)
(*   Proof. *)
(*     split. *)
(*     - intros H%(f_equal (@rev X)). now rewrite !rev_involutive in H. *)
(*     - now intros <-. *)
(*   Qed. *)

(*   Lemma rev_nil A: *)
(*     rev A = [] -> A = []. *)
(*   Proof. *)
(*     destruct A. auto. now intros H%symmetry%app_cons_not_nil. *)
(*   Qed. *)

(*   Lemma map_inj (Y:Type) A B (f: X -> Y) : *)
(*     Injective f -> map f A = map f B <-> A = B. *)
(*   Proof. *)
(*     intros inj. split. *)
(*     - revert B. induction A; intros B H; cbn in *; destruct B; auto; cbn in H; inv H. *)
(*       rewrite (inj a x H1). specialize (IHA B H2). now subst. *)
(*     - now intros <-. *)
(*   Qed. *)
(* End fix_X. *)


Lemma app_incl_l X (A B C : list X) :
  A ++ B <<= C -> A <<= C.
Proof.
  firstorder eauto.
Qed.

Lemma app_incl_R X (A B C : list X) :
  A ++ B <<= C -> B <<= C.
Proof.
  firstorder eauto.
Qed.

Lemma cons_incl X (a : X) (A B : list X) : a :: A <<= B -> A <<= B.
Proof.
  intros ? ? ?. eapply H. firstorder.
Qed.

Lemma incl_sing X (a : X) A : a el A -> [a] <<= A.
Proof.
  now intros ? ? [-> | [] ].
Qed.

Hint Resolve app_incl_l app_incl_R cons_incl incl_sing.


(* Hint Extern 4 (_ el map _ _) => eapply in_map_iff. *)
(* Hint Extern 4 (_ el filter _ _) => eapply filter_In. *)

(* Fixpoint count (l : list nat) (n : nat)  := *)
(*   match l with *)
(*   | [] => 0 *)
(*   | m :: l => if Nat.eqb n m then S (count l n) else count l n *)
(*   end. *)

(* Lemma countSplit (A B: list nat) (x: nat)  : count A x + count B x = count (A ++ B) x.  *)
(* Proof.  *)
(*   induction A.  *)
(*   - reflexivity.  *)
(*   - cbn. destruct (x =? a). *)
(*     + cbn. f_equal; exact IHA.  *)
(*     + exact IHA.  *)
(* Qed. *)

(* Lemma notInZero (x: nat) A : *)
(*   not (x el A) <-> count A x = 0. *)
(* Proof. *)
(*   split; induction A. *)
(*   -  reflexivity. *)
(*   - intros H. cbn in *. destruct (Nat.eqb_spec x a). *)
(*     + exfalso. apply H. left. congruence. *)
(*     + apply IHA. intros F. apply H. now right. *)
(*   - tauto. *)
(*   - cbn. destruct (Nat.eqb_spec x a). *)
(*     + subst a. omega. *)
(*     + intros H [E | E]. *)
(*       * now symmetry in E. *)
(*       * tauto. *)
(* Qed. *)


(** Positions and map-products for lists *)

Section Positions.
  Variables (X: Type) (d: forall x y : X, {x = y} + {x <> y}).
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

  Notation nthe n A := (nth_error A n).
  
  Lemma nthe_length A n :
    length A > n -> { x | nthe n A = Some x }.
  Proof.
    revert n.
    induction A as [|y A IH]; cbn; intros n H.
    - exfalso. omega.
    - destruct n as [|n]; cbn.
      + now exists y.
      + destruct (IH n) as [x H1]. omega. now exists x.
  Qed.
  
 Lemma pos_nthe x A n :
    pos x A = Some n -> nthe n A = Some x.
 Proof.
   revert n.
   induction A as [|y A IH]; cbn; intros n.
    - intros [=].
    - destruct (d x y) as [<-|H1].
      + now intros [= <-].
      + destruct (pos x A) as [k|]; intros [= <-]; cbn.
        now apply IH.
  Qed.
  
  Lemma nthe_app_l x n A B :
    nthe n A = Some x -> nthe n (A ++ B) = Some x.
  Proof.
    revert n.
    induction A as [|y A IH]; cbn; intros k H.
    - destruct k; discriminate H.
    - destruct k as [|k]; cbn in *. exact H.
      apply IH, H.
  Qed.

End Positions.

Notation nthe n A := (nth_error A n).

Lemma pos_nth X d (x : X) l n def : pos d x l = Some n -> nth n l def = x.
Proof.
  revert n; induction l; cbn; intros; try congruence.
  destruct (d x a); try destruct (pos d x l) eqn:E; inv H; eauto.
Qed.

Lemma pos_length X d (x : X) l n : pos d x l = Some n -> n < | l |.
Proof.
  revert n; induction l; cbn; intros; try congruence.
  destruct (d x a).
  - inv H. omega.
  - destruct (pos d x l) eqn:E; inv H; try omega. specialize (IHl _ eq_refl). omega.
Qed.


Fixpoint omap X Y (f : X -> option Y) l :=
  match l with
  | nil => nil
  | x :: l => match f x with Some y => y :: omap f l | None => omap f l end
  end.

Lemma in_omap_iff X Y (f : X -> option Y) l y : y el omap f l <-> exists x, x el l /\ f x = Some y.
Proof.
  induction l; cbn.
  - firstorder.
  - destruct (f a) eqn:E; firstorder (subst; firstorder congruence).
Qed.


Section neList.

  Variable X : Type.
  Variable P : list X -> Prop.

  Hypothesis B : (forall x : X, P [x]).
  Hypothesis S : (forall x A, P A -> P (x :: A)).
  
  Lemma list_ind_ne A : A <> [] -> P A.
  Proof.
    intros H. destruct A. congruence. clear H.
    revert x. induction A; eauto.
  Qed.

End neList.


(** ** Boolean propositions and decisions *)

Coercion bool2Prop (b : bool) := if b then True else False.

Lemma bool_Prop_true b :
  b = true -> b.
Proof.
  intros A. rewrite A. cbn. eauto.
Qed.

Lemma bool_Prop_false b :
  b = false -> ~ b.
Proof.
  intros A. rewrite A. cbn. auto.
Qed.

Hint Resolve bool_Prop_true bool_Prop_false.

Hint Extern 4 => 
match goal with
|[ H: False |- _ ] => destruct H
|[ H: ~ bool2Prop true |- _ ] => destruct H
|[ H: bool2Prop false |- _ ] => destruct H
|[ H: true=false |- _ ] => discriminate H
|[ H: false=true |- _ ] => discriminate H
|[ H: ?b=false, H': bool2Prop(?b) |- _ ] => rewrite H in H'; destruct H'
(* |[ H: ?x el nil |- _ ] => destruct H *)
end.

Definition dec (X: Prop) : Type := {X} + {~ X}.

Coercion dec2bool P (d: dec P) := if d then true else false.

Existing Class dec.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.


Ltac dec := repeat match goal with
                  | [ |- context [ Dec ?x ] ] => let E := fresh "E" in destruct (Dec x) as [E | ]; [ try (rewrite E in *; clear E)| ]
                  | [H : context [ Dec ?x ]  |- _ ] => let E := fresh "E" in destruct (Dec x) as [E | ];
                                                                      [ try (rewrite E in *; clear E)| ]
                  end; cbn [dec2bool].

Lemma Dec_reflect (X: Prop) (d: dec X) :
  Dec X <-> X.
Proof.
  destruct d as [A|A]; cbn; tauto.
Qed.

Notation Decb X := (dec2bool (Dec X)).

Lemma Dec_reflect_eq (X Y: Prop) (d: dec X) (e: dec Y) :
 Decb X = Decb Y <->  (X <-> Y).
Proof.
  destruct d as [D|D], e as [E|E]; cbn; intuition congruence.
Qed.

Lemma Dec_auto (X: Prop) (d: dec X) :
  X -> Dec X.
Proof.
  destruct d as [A|A]; cbn; tauto.
Qed.

Lemma Dec_auto_not (X: Prop) (d: dec X) :
  ~ X -> ~ Dec X.
Proof.
  destruct d as [A|A]; cbn; tauto.
Qed.

Hint Resolve Dec_auto Dec_auto_not.
Hint Extern 4 =>  (* Improves type class inference *)
match goal with
  | [  |- dec ((fun _ => _) _) ] => cbn
end : typeclass_instances.

Tactic Notation "decide" constr(p) := 
  destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (Dec p) as i.
Tactic Notation "decide" "_" :=
  destruct (Dec _).
Tactic Notation "have" constr(E) := let X := fresh "E" in decide E as [X|X]; subst; try congruence; try omega; clear X.

Lemma Dec_true P {H : dec P} : dec2bool (Dec P) = true -> P.
Proof.
  decide P; cbv in *; firstorder.
Qed.

Lemma Dec_false P {H : dec P} : dec2bool (Dec P) = false -> ~P.
Proof.
  decide P; cbv in *; firstorder.
Qed.

Hint Extern 4 =>
match goal with
  [ H : dec2bool (Dec ?P) = true  |- _ ] => apply Dec_true in  H
| [ H : dec2bool (Dec ?P) = false |- _ ] => apply Dec_false in H
end.

(** Decided propositions behave classically *)

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

(** Propagation rules for decisions *)

Fact dec_transfer P Q :
  P <-> Q -> dec P -> dec Q.
Proof.
  unfold dec. tauto.
Qed.

Instance bool_dec (b: bool) :
  dec b.
Proof. 
  unfold dec. destruct b; cbn; auto. 
Qed.

Instance True_dec :
  dec True.
Proof. 
  unfold dec; tauto. 
Qed.

Instance False_dec :
  dec False.
Proof. 
  unfold dec; tauto. 
Qed.

Instance impl_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X -> Y).
Proof. 
  unfold dec; tauto. 
Qed.

Instance and_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X /\ Y).
Proof. 
  unfold dec; tauto. 
Qed.

Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof. 
  unfold dec; tauto. 
Qed.

(* Coq standard modules make "not" and "iff" opaque for type class inference, 
   can be seen with Print HintDb typeclass_instances. *)

Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof. 
  unfold not. auto.
Qed.

Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof. 
  unfold iff. auto.
Qed.

(** ** Discrete types *)

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

Structure eqType := EqType {
  eqType_X :> Type;
  eqType_dec : eq_dec eqType_X }.

Arguments EqType X {_} : rename.

Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.

Existing Instance eqType_dec.

Instance unit_eq_dec :
  eq_dec unit.
Proof.
  unfold dec. decide equality. 
Qed.

Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  unfold dec. decide equality. 
Defined.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  unfold dec. decide equality.
Defined.

Instance prod_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  unfold dec. decide equality. 
Defined.

Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  unfold dec. decide equality. 
Defined.

Instance sum_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof.
  unfold dec. decide equality. 
Defined.

Instance option_eq_dec X :
  eq_dec X -> eq_dec (option X).
Proof.
  unfold dec. decide equality.
Defined.

Instance Empty_set_eq_dec:
  eq_dec Empty_set.
Proof.
  unfold dec. decide equality.
Qed.

Instance True_eq_dec:
  eq_dec True.
Proof.
  intros x y. destruct x,y. now left.
Qed.

Instance False_eq_dec:
  eq_dec False.
Proof.
  intros [].
Qed.

Export ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).
Definition equi X (A B : list X) : Prop := incl A B /\ incl B A.
Notation "A === B" := (equi A B) (at level 70).
Hint Unfold equi.

Hint Extern 4 => 
match goal with
|[ H: ?x el nil |- _ ] => destruct H
end.

(** ** Lists *)

(* Register additional simplification rules with autorewrite / simpl_list *)
(* Print Rewrite HintDb list. *)
Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.

Lemma list_cycle  (X : Type) (A : list X) x :
  x::A <> A.
Proof.
  intros B.
  assert (C: |x::A| <> |A|) by (cbn; omega).
  apply C. now rewrite B.
Qed.

(** *** Decisions for lists *)

Instance list_in_dec X (x : X) (A : list X) :  
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Qed.

(* Certifying find *)

Lemma cfind X A (p: X -> Prop) (p_dec: forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  destruct (find (fun x => Dec (p x)) A) eqn:E.
  - apply find_some in E. firstorder.
  - right. intros. eapply find_none in E; eauto.
Qed.

Arguments cfind {X} A p {p_dec}.

Instance list_forall_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
  intros p_dec.
  destruct (find (fun x => Dec (~ p x)) A) eqn:Eq.
  - apply find_some in Eq as [H1 H0 %Dec_true]; right; auto. 
  - left. intros x E. apply find_none with (x := x) in Eq. apply dec_DN; auto. auto.
Qed.

Instance list_exists_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros p_dec.
  destruct (find (fun x => Dec (p x)) A) eqn:Eq. (* New: eta expansion needed *)
  - apply find_some in Eq as [H0 H1 %Dec_true]. firstorder. (* New: Need firstorder here *)
  - right. intros [x [E F]]. apply find_none with (x := x) in Eq; auto. eauto. (* New: Why can't auto solve this? *)
Qed.

Lemma list_exists_DM X A  (p : X -> Prop) : 
  (forall x, dec (p x)) ->
  ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof. 
  intros D E. 
  destruct (find (fun x => Dec (p x)) A) eqn:Eq.
  + apply find_some in Eq as [? ?%Dec_true]. eauto.
  + exfalso. apply E. intros. apply find_none with (x := x) in Eq;  eauto. 
Qed.

Lemma list_exists_not_incl (X: eqType) (A B : list X) :
  ~ A <<= B -> exists x, x el A /\ ~ x el B.
Proof.
  intros E.
  apply list_exists_DM; auto.
  intros F. apply E. intros x G.
  apply dec_DN; auto.
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, dec (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (cfind A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Qed.



(** *** Membership

We use the following lemmas from Coq's standard library List.
- [in_eq :  x el x::A]
- [in_nil :  ~ x el nil]
- [in_cons :  x el A -> x el y::A]
- [in_or_app :  x el A \/ x el B -> x el A++B]
- [in_app_iff :  x el A++B <-> x el A \/ x el B]
- [in_map_iff :  y el map f A <-> exists x, f x = y /\ x el A]
*)

Hint Resolve in_eq in_nil in_cons in_or_app.

Section Membership.
  Variable X : Type.
  Implicit Types (x y: X) (A B: list X).

  Lemma in_sing x y :
    x el [y] -> x = y.
  Proof. 
    cbn. intros [[]|[]]. reflexivity. 
  Qed.

  Lemma in_cons_neq x y A :
    x el y::A -> x <> y -> x el A.
  Proof. 
    cbn. intros [[]|D] E; congruence. 
  Qed.

  Lemma not_in_cons x y A :
    ~ x el y :: A -> x <> y /\ ~ x el A.
  Proof.
    intuition; subst; auto.
  Qed.

(** *** Disjointness *)

  Definition disjoint A B :=
    ~ exists x, x el A /\ x el B.

  Lemma disjoint_forall A B :
    disjoint A B <-> forall x, x el A -> ~ x el B.
  Proof.
    split.
    - intros D x E F. apply D. exists x. auto.
    - intros D [x [E F]]. exact (D x E F).
  Qed.

  Lemma disjoint_symm A B :
    disjoint A B -> disjoint B A.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_incl A B B' :
    B' <<= B -> disjoint A B -> disjoint A B'.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil B :
    disjoint nil B.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil' A :
    disjoint A nil.
  Proof.
    firstorder.
  Qed.
  
  Lemma disjoint_cons x A B :
    disjoint (x::A) B <-> ~ x el B /\ disjoint A B.
  Proof.
    split.
    - intros D. split.
      + intros E. apply D. eauto.
      + intros [y [E F]]. apply D. eauto.
    - intros [D E] [y [[F|F] G]]. 
      + congruence.
      + apply E. eauto.
  Qed.

  Lemma disjoint_app A B C :
    disjoint (A ++ B) C <-> disjoint A C /\ disjoint B C.
  Proof.
    split.
    - intros D. split.
      + intros [x [E F]]. eauto 6.
      + intros [x [E F]]. eauto 6.
    - intros [D E] [x [F G]]. 
      apply in_app_iff in F as [F|F]; eauto.
  Qed.

End Membership.

Hint Resolve disjoint_nil disjoint_nil'.

(** *** Inclusion

We use the following lemmas from Coq's standard library List.
- [incl_refl :  A <<= A]
- [incl_tl :  A <<= B -> A <<= x::B]
- [incl_cons : x el B -> A <<= B -> x::A <<= B]
- [incl_appl : A <<= B -> A <<= B++C]
- [incl_appr : A <<= C -> A <<= B++C]
- [incl_app : A <<= C -> B <<= C -> A++B <<= C]
*)

Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app.

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

  Proof. auto. Qed.

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

  Lemma incl_app_left A B C :
    A ++ B <<= C -> A <<= C /\ B <<= C.
  Proof.
    firstorder.
  Qed.

End Inclusion.

Definition inclp (X : Type) (A : list X) (p : X -> Prop) : Prop :=
  forall x, x el A -> p x.

(** *** Setoid rewriting with list inclusion and list equivalence *)

Instance incl_preorder X : 
  PreOrder (@incl X).
Proof. 
  constructor; hnf; unfold incl; auto. 
Qed.

Instance equi_Equivalence X : 
  Equivalence (@equi X).
Proof. 
  constructor; hnf; firstorder. 
Qed.

Instance incl_equi_proper X : 
  Proper (@equi X ==> @equi X ==> iff) (@incl X).
Proof. 
  hnf. intros A B D. hnf. firstorder. 
Qed.

Instance cons_incl_proper X x : 
  Proper (@incl X ==> @incl X) (@cons X x).
Proof.
  hnf. apply incl_shift.
Qed.

Instance cons_equi_proper X x : 
  Proper (@equi X ==> @equi X) (@cons X x).
Proof. 
  hnf. firstorder.
Qed.

Instance in_incl_proper X x : 
  Proper (@incl X ==> Basics.impl) (@In X x).
Proof.
  intros A B D. hnf. auto.
Qed.

Instance in_equi_proper X x : 
  Proper (@equi X ==> iff) (@In X x).
Proof. 
  intros A B D. firstorder. 
Qed.

Instance app_incl_proper X : 
  Proper (@incl X ==> @incl X ==> @incl X) (@app X).
Proof. 
  intros A B D A' B' E. auto.
Qed.

Instance app_equi_proper X : 
  Proper (@equi X ==> @equi X ==> @equi X) (@app X).
Proof. 
  hnf. intros A B D. hnf. intros A' B' E.
  destruct D, E; auto.
Qed.

Section Equi.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma equi_push x A :
    x el A -> A === x::A.
  Proof.
    auto.
  Qed.

  Lemma equi_dup x A :
    x::A === x::x::A.

  Proof.
    auto.
  Qed.

  Lemma equi_swap x y A:
    x::y::A === y::x::A.
  Proof.
    split; intros z; cbn; tauto.
  Qed.

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
    split; intros y; cbn.
    - intros [D|D]; subst; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + apply in_sing in D. auto.
  Qed.
  
End Equi.

Lemma in_concat_iff A l (a:A) : a el concat l <-> exists l', a el l' /\ l' el l.
Proof.
  induction l; cbn.
  - intuition. now destruct H. 
  - rewrite in_app_iff, IHl. firstorder subst. auto. (* TODO: find something faster than firstorder subst *)
Qed.



(** *** Filter *)

Section Filter.
  Variable X : Type.
  Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
  
  Fixpoint filter p A : list X :=
    match A with
    | nil => nil
    | x::A' => if p x then x :: filter p A' else filter p A'
    end.

  Lemma in_filter_iff x p A :
    x el filter p A <-> x el A /\ p x.
  Proof. 
    induction A as [|y A]; cbn.
    - tauto.
    - destruct (p y) eqn:E; cbn;
      rewrite IHA; intuition; subst; auto.
  Qed.

  Lemma filter_incl p A :
    filter p A <<= A.  
  Proof.
    intros x D. apply in_filter_iff in D. apply D.
  Qed.

  Lemma filter_mono p A B :
    A <<= B -> filter p A <<= filter p B.
  Proof.
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_id p A :
    (forall x, x el A -> p x) -> filter p A = A.
  Proof.
    intros D.
    induction A as [|x A]; cbn.
    - reflexivity.
    - destruct (p x) eqn:E.
      + f_equal; auto.
      + exfalso. apply bool_Prop_false in E. auto.
  Qed.

  Lemma filter_app p A B :
    filter p (A ++ B) = filter p A ++ filter p B.
  Proof.
    induction A as [|y A]; cbn.
    - reflexivity.
    - rewrite IHA. destruct (p y); reflexivity.  
  Qed.

  Lemma filter_fst p x A :
    p x -> filter p (x::A) = x::filter p A.
  Proof.
    cbn. destruct (p x); auto.
  Qed.

  Lemma filter_fst' p x A :
    ~ p x -> filter p (x::A) = filter p A.
  Proof.
    cbn. destruct (p x); auto.
  Qed.

  Lemma filter_pq_mono p q A :
    (forall x, x el A -> p x -> q x) -> filter p A <<= filter q A.
  Proof. 
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_pq_eq p q A :
    (forall x, x el A -> p x = q x) -> filter p A = filter q A.
  Proof. 
    intros C; induction A as [|x A]; cbn.
    - reflexivity.
    - destruct (p x) eqn:D, (q x) eqn:E.
      + f_equal. auto.
      + exfalso. enough (p x = q x) by congruence. auto.
      + exfalso. enough (p x = q x) by congruence. auto.
      + auto.
  Qed.

  Lemma filter_and p q A :
    filter p (filter q A) = filter (fun x => p x && q x) A.
  Proof.
    induction A as [|x A]; cbn. reflexivity.
    destruct (p x) eqn:E, (q x); cbn;
      try rewrite E; now rewrite IHA.
  Qed.

  Lemma filter_comm p q A :
    filter p (filter q A) = filter q (filter p A).
  Proof.
    rewrite !filter_and. apply filter_pq_eq.
    intros x _. now destruct (p x), (q x).
  Qed.
  
End Filter.


(** *** Element removal *)

Section Removal.
  Variable X : eqType.
  Implicit Types (x y: X) (A B: list X).

  Definition rem A x : list X :=
    filter (fun z => Dec (z <> x)) A.

  Lemma in_rem_iff x A y :
    x el rem A y <-> x el A /\ x <> y.
  Proof.
    unfold rem. rewrite in_filter_iff, Dec_reflect. tauto.
  Qed.

  Lemma rem_not_in x y A :
    x = y \/ ~ x el A -> ~ x el rem A y.
  Proof.
    unfold rem. rewrite in_filter_iff, Dec_reflect. tauto.
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

  Lemma rem_app' x A B C :
    rem A x <<= C -> rem B x <<= C -> rem (A ++ B) x <<= C.
  Proof.
    unfold rem; rewrite filter_app; auto.
  Qed.

  Lemma rem_equi x A :
    x::A === x::rem A x.
  Proof.
    split; intros y; 
    intros [[]|E]; decide (x=y) as [[]|D]; 
    eauto using rem_in, rem_neq. 
  Qed.

  Lemma rem_comm A x y :
    rem (rem A x) y = rem (rem A y) x.
  Proof.
    apply filter_comm.
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

  Lemma rem_id x A :
    ~ x el A -> rem A x = A.
  Proof.
    intros D. apply filter_id. intros y E.
    apply Dec_reflect. congruence.
  Qed.

  Lemma rem_reorder x A :
    x el A -> A === x :: rem A x.
  Proof.
    intros D. rewrite <- rem_equi. apply equi_push, D.
  Qed.

  Lemma rem_inclr A B x :
    A <<= B -> ~ x el A -> A <<= rem B x.
  Proof.
    intros D E y F. apply in_rem_iff.
    intuition; subst; auto. 
  Qed.

End Removal.

Hint Resolve rem_not_in rem_incl rem_mono rem_cons rem_cons' rem_app rem_app' rem_in rem_neq rem_inclr.


Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).

Notation "[ s | p ∈ A ',' P ]" :=
  (map (fun p => s) (filter (fun p => Dec P) A)) (p pattern).
Notation "[ s | p ∈ A ]" :=
  (map (fun p => s) A) (p pattern).

Ltac in_app n :=
  (match goal with
  | [ |- _ el _ ++ _ ] => 
    match n with
    | 0 => idtac
    | 1 => eapply in_app_iff; left
    | S ?n => eapply in_app_iff; right; in_app n
    end
  | [ |- _ el _ :: _ ] => match n with 0 => idtac | 1 => left | S ?n => right; in_app n end
  end) || (repeat (try right; eapply in_app_iff; right)).

Lemma to_dec (P : Prop) `{dec P} : P <-> Dec P.
Proof.
  firstorder. destruct (Dec P); cbn in *; firstorder.
Qed.

Ltac in_collect a :=
  eapply in_map_iff; exists a; split; [ eauto | match goal with [ |- _ el filter _ _ ] =>  eapply in_filter_iff; split; [ try (rewrite !in_prod_iff; repeat split) | rewrite <- to_dec; repeat split; eauto ] | _ => try (rewrite !in_prod_iff; repeat split) end ].
Ltac inv_collect :=
  repeat
    (match goal with
    | [ H : ?x el concat _ |- _ ] => eapply in_concat_iff in H as (? & ? & ?)
    | [ H : ?x el map _ _ |- _ ] => let x := fresh "x" in eapply in_map_iff in H as (x & ? & ?)
    | [ x : ?A * ?B |- _ ] => destruct x; subst
    | [ H : ?x el filter _ _ |- _ ] => let H' := fresh "H" in eapply in_filter_iff in H as (? & H' % to_dec)
    | [ H : ?x el list_prod _ _ |- _ ] => eapply in_prod_iff in H
    | [ H : _ el _ ++ _ |- _ ] => try eapply in_app_iff in H as []
    | [H : _ el _ :: _ |- _ ] => destruct H
     end; intuition; subst).
