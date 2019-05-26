Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
Require Import Classes.RelationClasses Classes.Morphisms List Tactics.
From mathcomp Require Import ssrfun ssrbool ssrnat seq.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* There are similar definitions in the Ensembles library (Included
   and Same_set); set_eq is not exactly the same as Same_set though
   (only logically equivalent). *)

Definition set T := T -> Prop.

Notation "x \in A" := (A x) (at level 70, only parsing) : set_scope.

Definition set_eq {A} (m1 m2 : set A) :=
  forall (a : A), m1 a <-> m2 a.

Infix "<-->" := set_eq (at level 70, no associativity) : set_scope.

Open Scope set_scope.

Lemma set_eq_trans T B (A C : set T) : A <--> B -> B <--> C -> A <--> C.
Proof.
by move=> eqAB eqBC; split=> [/eqAB/eqBC|/eqBC/eqAB].
Qed.

Lemma set_eq_symm {A} (s1 s2 : set A) :
  s1 <--> s2 -> s2 <--> s1.
Proof.
  firstorder.
Qed.

Lemma set_eq_refl {A} (s : set A) :
  s <--> s.
Proof.
  firstorder.
Qed.


Global Instance : forall T, Equivalence (@set_eq T).
Proof.
move=> T; constructor=> // [A B eqAB | A B C] x; first by split=> /eqAB.
exact: set_eq_trans.
Qed.

Definition set_incl {A} (m1 m2 : set A) :=
  forall (a : A), m1 a -> m2 a.

Infix "\subset" := set_incl (at level 70, no associativity) : set_scope.

Notation "[ 'set' x : T | P ]" := (fun x : T => P)
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]", only parsing) : set_scope.

Definition set0 {T} := [set _ : T | False].

Definition setT {T} := [set _ : T | True].

Notation "[ 'set' : T ]" := (@setT T)
  (at level 0, format "[ 'set' :  T ]") : set_scope.

Section setOpsDef.

Context {T U : Type}.
Implicit Types (a x : T) (A B : set T).

Definition set1 a := eq a.

Definition setU A B := [set x | x \in A \/ x \in B].

Definition setI A B := [set x | x \in A /\ x \in B].

Definition codom (f : T -> U) := [set y | exists x, f x = y].

Definition bigcup A (F : T -> set U) := [set x | exists i, i \in A /\ x \in F i].

Definition bigcap (A : set T) (F : T -> set U) :=
  [set x | forall (i : T), i \in A -> x \in F i].

End setOpsDef.

Definition imset {T U} (f : T -> U) A := bigcup A (fun x => set1 (f x)).

Definition setX T U (A : set T) (B : set U) := [set x | x.1 \in A /\ x.2 \in B].

Definition imset2 T U V (f : T -> U -> V) A1 A2 :=
  imset (prod_curry f) (setX A1 A2).

Definition codom2 T U V (f : T -> U -> V) := codom (prod_curry f).

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : set_scope.

Notation "A :|: B" := (setU A B) (at level 52, left associativity) : set_scope.
Notation "a |: A" := ([set a] :|: A) (at level 52, left associativity) : set_scope.

Notation "A :&: B" := (setI A B) (at level 48, left associativity) : set_scope.

Notation "f @: A" := (imset f A) (at level 24) : set_scope.

Notation "f @2: ( A , B )" := (imset2 f A B)
  (at level 24, format "f  @2:  ( A ,  B )") : set_scope.

Notation "\bigcup_ i F" := (bigcup setT (fun i => F))
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'") : set_scope.
Notation "\bigcup_ ( i : t ) F" := (bigcup (@setT t) (fun i => F))
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t ) '/  '  F ']'", only parsing) : set_scope.
Notation "\bigcup_ ( i 'in' A ) F" := (bigcup A (fun i => F))
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A ) '/  '  F ']'") : set_scope.

Notation "\bigcap_ ( i 'in' A ) F" := (bigcap A (fun i => F))
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcap_ ( i  'in'  A ) '/  '  F ']'") : set_scope.

Definition lift {T} (S : set T) : set (option T) :=
  Some @: S :|: [set None].

Lemma subset_eqP T (A B : set T) : (A <--> B) <-> (A \subset B /\ B \subset A).
Proof.
split; first by move=> eqAB; split=> a; rewrite (eqAB a).
by case=> subAB subBA a; split; [apply: subAB | apply:subBA].
Qed.

Lemma subset_trans T (A1 A2 A3 : set T) :
  A1 \subset A2 ->
  A2 \subset A3 ->
  A1 \subset A3.
Proof.
  now firstorder.
Qed.

Lemma subset_refl T (A : set T) : A \subset A.
Proof.
    by rewrite /set_incl.
Qed.

Lemma subset_singl : 
  forall {T} (x y : T), [set x] \subset [set y] <-> y = x. 
Proof.
  intros. split; intros H; subst; auto.  
  - apply H; reflexivity.
  - apply subset_refl.
Qed.

Lemma subset_respects_set_eq_l :
  forall (T : Type) (s1 s2 s3 : set T),
    s1 <--> s3 -> s3 \subset s2 -> s1 \subset s2.
Proof.
  now firstorder.
Qed.

Lemma subset_respects_set_eq_r :
  forall (T : Type) (s1 s2 s3 : set T),
    s3 <--> s2 -> s1 \subset s2 -> s1 \subset s3.
Proof.
  now firstorder.
Qed.

Lemma subset_respects_set_eq :
  forall {T : Type} {s1 s2 s1' s2' : set T},
    s1 <--> s1' ->
    s2 <--> s2' ->
    s1' \subset s2' ->
    s1 \subset s2.
Proof.
  firstorder.
Qed.

Lemma imsetT T U (f : T -> U) : f @: setT <--> codom f.
Proof.
  move=> y; split; first by case=> x [_ fx]; exists x.
    by case=> x fx; exists x.
Qed.

Lemma imset_id T (A : set T) : id @: A <--> A.
Proof.
    by move=> t; split=> [[x [Ax <-]]|At] //; exists t.
Qed.

Lemma imset_incl {T U} (A B : set T) (f : T -> U):
  A \subset B -> 
  f @: A \subset f @: B.
Proof.
  move => H u [x [H1 H2]]. eexists; split; eauto.
Qed.

Lemma imset_eq {T U} (A B : set T) (f : T -> U):
  A <--> B -> 
  f @: A <--> f @: B.
Proof.
  move => H u. split; apply imset_incl => t Ht; by apply H.
Qed.

Lemma imset_in a b x (f : a -> b) (A : set a) :
  x \in A -> f x \in (f @: A).
Proof.
  intros. unfold imset. exists x. split; by [].
Qed.

Lemma imset_id_ext T (A : set T) f : (forall x, f x = x) -> f @: A <--> A.
Proof.
  rewrite /imset /bigcup => H x. split.
  - move => [y [H1 H2]]. rewrite H in H2. inversion H2. subst. assumption.
  - move => H1. eexists. split. eassumption. by rewrite H.
Qed.

Lemma imset_eq_ext a b (f g : a -> b) (A : set a) :
  (forall x, f x = g x) ->
  f @: A <--> g @: A.
Proof.
  rewrite /imset /bigcup /set1. move => H x.
  split => [[i [H1 H2]] | [i [H1 H2]]]; eexists; split;
           try eassumption. congruence. congruence.
Qed.

Lemma coverE T (A : set T) : \bigcup_(x in A) [set x] <--> A.
Proof. exact: imset_id. Qed.

Lemma setXT T U : setX [set: T] [set: U] <--> [set: T * U].
Proof. by case. Qed.

Instance set_incl_Proper T U :
  Proper (@eq (T -> U) ==> set_incl ==> set_incl) imset.
Proof.
by move=> f ? <- A B subAB y [x [Ax fx]]; exists x; split=> //; apply: subAB.
Qed.

Instance set_eq_Proper T U : Proper (@eq (T -> U) ==> set_eq ==> set_eq) imset.
Proof.
by move=> f ? <- A B /subset_eqP[subAB subBA] y; split; apply: set_incl_Proper.
Qed.

Lemma sub0set T (A : set T) : set0 \subset A.
Proof. by []. Qed.

Lemma bigcup_set0 T U (F : T -> set U) :
  \bigcup_(x in set0) F x <--> set0.
Proof. by move=> t; split=> // [[? []]]. Qed.

Lemma imset0 T U (f : T -> U) : f @: set0 <--> set0.
Proof. exact: bigcup_set0. Qed.

Lemma bigcup_set1 T U (F : T -> set U) y :
  \bigcup_(x in [set y]) F x <--> F y.
Proof. by move=> t; split=> [[y' [<-]] | Fyt] //; exists y. Qed.

Lemma bigcup_setU_l:
  forall (U T : Type) (s1 s2 : set U) (f : U -> set T),
  \bigcup_(i in (s1 :|: s2)) f i <-->
  \bigcup_(i in s1) f i :|: \bigcup_(i in s2) f i.
Proof.
  firstorder.
Qed.

Lemma bigcup_const A B (P : set B) : inhabited A -> (\bigcup_(_ : A) P) <--> P.
Proof. by case=> a x; split=> [[?] []|Px] //; exists a. Qed.

Lemma bigcup_const_2 A (x :A) B (P : set B) : (\bigcup_(_ in [set x]) P) <--> P.
Proof. by split=> [[?] []|Px] //; exists x; split => //=. Qed.

Lemma bigcupC T U V A B (F : T -> U -> set V) :
  \bigcup_(i in A) \bigcup_(j in B) F i j <-->
  \bigcup_(j in B) \bigcup_(i in A) F i j.
Proof.
  wlog suff: T U A B F / \bigcup_(i in A) \bigcup_(j in B) F i j \subset
   \bigcup_(j in B) \bigcup_(i in A) F i j.
  by move=> sub; apply/subset_eqP; split; apply: sub.
    by move=> x [i [Ai [j [Bj ?]]]]; exists j; split=> //; exists i.
Qed.

Lemma incl_bigcupr T U A (F : T -> set U) G : (forall x, F x \subset G x) ->
  \bigcup_(x in A) F x \subset \bigcup_(x in A) G x.
Proof.
  by move=> subFG t [x [Ax Fxt]]; exists x; split=> //; apply: subFG.
Qed.

Lemma eq_bigcupr T U A (F : T -> set U) G : (forall x, F x <--> G x) ->
  \bigcup_(x in A) F x <--> \bigcup_(x in A) G x.
Proof.
  by move=> eq_FG t; split; apply: incl_bigcupr => {t} x t; rewrite (eq_FG x t).
Qed.

Lemma incl_bigcupl T U A B (F : T -> set U) : A \subset B ->
  \bigcup_(x in A) F x \subset \bigcup_(x in B) F x.
Proof.
    by move=> subAB t [x [Ax Fxt]]; exists x; split=> //; apply: subAB.
Qed.

Lemma eq_bigcupl T U A B (F : T -> set U) : A <--> B ->
  \bigcup_(x in A) F x <--> \bigcup_(x in B) F x.
Proof.
  by move=> /subset_eqP[? ?]; split; apply: incl_bigcupl.
Qed.

Lemma incl_bigcup a b (x:a) (A : set a) (f:a->set b) :
  x \in A -> 
  f x \subset \bigcup_(x in A) f x.
Proof.
  rewrite /set_incl /bigcup. by eauto 3.
Qed.


Arguments eq_bigcupl [T U A] B F _ _.

Global Instance eq_bigcup T U : Proper (set_eq ==> pointwise_relation T (@set_eq U) ==> set_eq) bigcup.
Proof.
  move=> A B eqAB F G eqFG a; apply: (@set_eq_trans _ (\bigcup_(i in A) G i)).
  exact: eq_bigcupr.
  exact: eq_bigcupl.
Qed.

Lemma bigcup_flatten T U V A (F : T -> set U) (G : U -> set V) :
  \bigcup_(x in \bigcup_(y in A) F y) G x <-->
  \bigcup_(y in A) \bigcup_(x in F y) G x.
Proof.
move=> t; split=> [[x [[y [Ay Fyx]] Gxt]] | [y [Ay [x [Fyx Gxt]]]]].
  by exists y; split=> //; exists x.
by exists x; split=> //; exists y.
Qed.

Lemma codom_apply {A B : Type} {f : A -> B} {x : A} : f x \in codom f.
Proof. eexists; eauto. Qed.

Lemma codomE T U (f : T -> U) : codom f <--> \bigcup_x [set f x].
Proof. by move=> y; split=> [[x fx]|[x [_ fx]]]; exists x. Qed.

Lemma codom_id T : codom id <--> [set: T].
Proof. by move=> x; split=> // _; exists x. Qed.

Lemma codom_const A B (x : B) : inhabited A ->
  codom (fun _ : A => x) <--> [set x].
Proof. by move=> ?; rewrite codomE bigcup_const. Qed.

Lemma imset_comp T U V (f : U -> T) (g : V -> U) A :
  (f \o g) @: A <--> f @: (g @: A).
Proof.
by rewrite /imset bigcup_flatten; apply: eq_bigcupr => x; rewrite bigcup_set1.
Qed.

Lemma codom_comp T U V (f : U -> T) (g : V -> U) :
  codom (f \o g) <--> f @: (codom g).
Proof. by rewrite -imsetT imset_comp imsetT. Qed.

Lemma curry_imset2l T U V (f : T -> U -> V) A1 A2 :
  f @2: (A1, A2) <--> \bigcup_(x1 in A1) f x1 @: A2.
Proof.
move=> a; split.
  by case=> [[x1 x2] [[/= Ax1 Ax2] fx]]; exists x1; split=> //; exists x2.
by case=> [x1 [Ax1 [x2 [Ax2 fx]]]]; exists (x1,x2).
Qed.

Lemma curry_imset2r T U V (f : T -> U -> V) A1 A2 :
  f @2: (A1, A2) <--> \bigcup_(x2 in A2) f^~ x2 @: A1.
Proof. by rewrite curry_imset2l bigcupC. Qed.

Lemma curry_codom2l T U V (f : T -> U -> V) :
  codom (prod_curry f) <--> \bigcup_x1 codom (f x1).
Proof.
rewrite -imsetT -setXT -/(imset2 f _ _) curry_imset2l.
by apply: eq_bigcupr => x; rewrite imsetT.
Qed.

Lemma imset_bigcup T U V (f : U -> V) A (F : T -> set U) :
  (f @: \bigcup_(x in A) (F x)) <--> \bigcup_(x in A) f @: F x.
Proof. by rewrite /imset bigcup_flatten. Qed.

Lemma bigcup_imset T U V (f : T -> U) A (F : U -> set V) :
  \bigcup_(y in f @: A) (F y) <--> \bigcup_(x in A) F (f x).
Proof.
by rewrite bigcup_flatten; apply: eq_bigcupr => x; rewrite bigcup_set1.
Qed.

Lemma bigcup_codom T U V (f : T -> U) (F : U -> set V) :
  \bigcup_(y in codom f) (F y) <--> \bigcup_x F (f x).
Proof. by rewrite -imsetT bigcup_imset. Qed.

Coercion seq_In T : seq T -> set T := fun s x => List.In x s.
Coercion list_In T : list T -> set T := fun s x => List.In x s.

Lemma subnilset T (A : set T) : [::] \subset A.
Proof. by []. Qed.

Lemma subconsset T (A : set T) x s :
  x :: s \subset A <-> x \in A /\ s \subset A.
Proof.
split=> [sub|[Ax sub] a [<-|?]] //; last by apply: sub.
split=> [|a sa]; apply: sub; first by left.
by right.
Qed.

Lemma reindex_bigcup I J K (h : J -> I) (F : I -> set K) A B :
  h @: B <--> A ->
  \bigcup_(x in A) F x <--> \bigcup_(y in B) F (h y).
Proof.
move=> surj t; split.
  case=> x [Ax Fxt]; case: (surj x) => [?].
  by case=> // y [By eq_hyx]; exists y; rewrite eq_hyx.
case=> y [By Fhyt]; exists (h y); split=> //.
by case: (surj (h y)) => Ahy _; apply: Ahy; exists y.
Qed.
Arguments reindex_bigcup [I J K] h [F A] B _ _.

Lemma bigcup_pointwise_incl A B (s : set A) (t : A -> set B) (u : set B) :
  (forall x, x \in s -> t x \subset u) ->
  \bigcup_(x in s) t x \subset u.
Proof.
  intros H b [x []]; eapply H; eauto.
Qed.

Instance proper_set_incl A :
  Morphisms.Proper (set_eq ==> set_eq ==> Basics.impl) (@set_incl A).
Proof. firstorder. Qed.

(** Lemmas about [setU] and [setI] *)

Instance eq_setU U : Proper (set_eq ==> set_eq ==> set_eq) (@setU U).
Proof.
  move=> A B eqAB F G eqFG a.
  split; by move => [H1 | H2]; firstorder.
Qed.

Instance eq_setI U : Proper (set_eq ==> set_eq ==> set_eq) (@setI U).
Proof.
  move=> A B eqAB F G eqFG a.
  by split; move => [H1 H2]; firstorder.
Qed.

Lemma setI_comm {U} (s1 s2 : set U) : 
   s1 :&: s2 <--> s2 :&: s1.
Proof.
  firstorder.
Qed.

Lemma setU_comm {U} (s1 s2 : set U) : 
   s1 :|: s2 <--> s2 :|: s1.
Proof.
  firstorder.
Qed.

Lemma setI_set0_abs {U} (s : set U) :
  (s :&: set0) <--> set0.
Proof.
  firstorder.
Qed.

Lemma setU_set0_neut {U} (s : set U) :
  (s :|: set0) <--> s.
Proof.
  firstorder.
Qed.

Lemma setU_set0_neut_eq {A} (s s1 : set A) :
  s1 <--> set0 ->
  s <--> s :|: s1.
Proof.
  firstorder.
Qed.

Lemma setU_set0_l {A} (s1 s2 s3 : set A) :
  s1 <--> set0 ->
  s2 <--> s3 ->
  (s1 :|: s2) <--> s3. 
Proof.
  firstorder.
Qed.

Lemma setU_set0_r {A} (s1 s2 s3 : set A) :
  s1 <--> set0 ->
  s3 <--> s2 ->
  s3 <--> (s1 :|: s2). 
Proof.
  firstorder.
Qed.

Lemma setI_setT_neut {U} (s : set U) :
  (s :&: setT) <--> s.
Proof.
  firstorder.
Qed.

Lemma setU_setT_abs {U} (s : set U) :
  (s :|: setT) <--> setT.
Proof.
  firstorder.
Qed.

Lemma setU_set_eq_compat {T} (s1 s2 s1' s2' : set T) :
  s1 <--> s1' ->
  s2 <--> s2' ->
  s1 :|: s2 <--> s1' :|: s2'.
Proof.
  by firstorder.
Qed.

Lemma setU_set_subset_compat :
  forall (T : Type) (s1 s2 s1' s2' : set T),
    s1 \subset s1' -> s2 \subset s2' -> s1 :|: s2 \subset s1' :|: s2'.
Proof.
  now firstorder.
Qed.

Lemma setU_set_incl_r :
  forall (T : Type) (s1 s2 s2' : set T),
    s1 \subset s2' -> s1 \subset s2 :|: s2'.
Proof.
  now firstorder.
Qed.

Lemma setU_assoc {U} (s1 s2 s3 : set U) :
  (s1 :|: (s2 :|: s3)) <--> ((s1 :|: s2) :|: s3).
Proof.
  firstorder.
Qed.

Lemma setI_assoc {U} (s1 s2 s3 : set U) :
  (s1 :&: (s2 :&: s3)) <--> ((s1 :&: s2) :&: s3).
Proof.
  firstorder.
Qed.

Lemma setI_impl_l {T} (s1 s2 : set T) : s1 \subset s2 -> s1 :&: s2 <--> s1.
Proof.      
  firstorder.
Qed.      

Lemma setI_impl_r {T} (s1 s2 : set T) : s2 \subset s1 -> s1 :&: s2 <--> s2.
Proof.      
  firstorder.
Qed.      

Lemma setI_set0 {U} (s1 s2 : set U) : 
  (forall x, s1 x -> ~ s2 x) ->
  (s1 :&: s2) <--> set0.
Proof.
  intros; split; firstorder. 
Qed.

Lemma setI_subset_compat {U} (s1 s2 s1' s2' : set U) : 
  s1 \subset s1' ->
  s2 \subset s2' ->
  (s1 :&: s2) \subset (s1' :&: s2').
Proof.
  firstorder.
Qed.

Lemma setU_subset_r {U} (s1 s2 s3 : set U) : 
  s1 \subset s3 ->
  s1 \subset (s2 :|: s3).
Proof.
  firstorder.
Qed.

Lemma setU_subset_l {U} (s1 s2 s3 : set U) : 
  s1 \subset s2 ->
  s1 \subset (s2 :|: s3).
Proof.
  firstorder.
Qed.

Lemma setI_setU_distr {U} (s1 s2 s3 : set U) : 
  ((s1 :|: s2) :&: s3) <--> ((s1 :&: s3) :|: (s2 :&: s3)).
Proof.
  firstorder.
Qed.

(** Lemmas about [bigcap] *)

Lemma bigcap_set0 (T U : Type) (F : T -> set U) :
  \bigcap_(x in set0) F x <--> setT.
Proof.
  split.
  - move => _. constructor.
  - move => _ x H. inversion H.
Qed.

Lemma incl_bigcapl T U A B (F : T -> set U) : B \subset A ->
  \bigcap_(x in A) F x \subset \bigcap_(x in B) F x.
Proof.
  by move => Hsub t Hcap x HB; eauto.
Qed.


Lemma eq_bigcapr (T U : Type) (A : set T) (F G : T -> set U) :
  (forall x : T, F x <--> G x) ->
  \bigcap_(x in A) F x <--> \bigcap_(x in A) G x.
Proof.
  by move => H a; split; move => Ha b Hb; eapply H; eauto.
Qed.

Lemma eq_bigcapl T U A B (F : T -> set U) : A <--> B ->
  \bigcap_(x in A) F x <--> \bigcap_(x in B) F x.
Proof.
  by move => H a; split; move => Ha b Hb; eapply Ha; eapply H; eauto.
Qed.


Instance eq_bigcap T U : Proper (set_eq ==> pointwise_relation T (@set_eq U) ==> set_eq) bigcap.
Proof.
  move=> A B eqAB F G eqFG a. apply: (@set_eq_trans _ (\bigcap_(i in A) G i)).
  exact: eq_bigcapr.
  exact: eq_bigcapl.
Qed.


Lemma eq_bigcup' :
  forall (T U : Type) (A B : set T) (F G : T -> set U),
    A <--> B ->
    (forall x, F x <--> G x) ->
    \bigcup_(x in A) F x <--> \bigcup_(x in B) G x.
Proof.
  intros.
  eapply eq_bigcup; eauto.
Qed.

Lemma incl_bigcup_compat :
  forall (T U : Type) (A B : set T) (F G : T -> set U),
    A \subset B ->
    (forall x : T, F x \subset G x) ->
    \bigcup_(x in A) F x \subset \bigcup_(x in B) G x.
Proof. 
  now firstorder. 
Qed.

Lemma bigcap_setI_l {U T} (s1 s2 : set U) (f : U -> set T) :
  bigcap (s1 :|: s2) f <-->
  bigcap s1 f :&: bigcap s2 f.
Proof.
  firstorder.
Qed.

Lemma bigcap_setU_l {U T} (s1 s2 : set U) (f : U -> set T) :
  bigcap s1 f \subset bigcap (s1 :&: s2) f.
Proof.
  firstorder.
Qed.

Lemma bigcap_set1 {U T} (x : U) (f : U -> set T) :
  bigcap [set x] f <--> f x.
Proof.
  split; move => H.
  eapply H. reflexivity.
  intros y Hy. inversion Hy. subst.
  assumption.
Qed.

Lemma bigcup_set0_r (T U : Type) (s : set T) (F : T -> set U) :
  (forall x, F x <--> set0) ->
  \bigcup_(x in s) F x <--> set0.
Proof.
  firstorder.
Qed.

Lemma bigcup_set0_l_eq (T U : Type) (s : set T) (F : T -> set U) :
  s <--> set0 ->
  \bigcup_(x in s) F x <--> set0.
Proof.
  firstorder.
Qed.

(** Lemmas about lists *)
Lemma nil_set_eq {A : Type} :
  [::] <--> (@set0 A).
Proof.
  split; move => H; eauto.
Qed.

Lemma cons_set_eq {A} (x : A) l :
  (x :: l) <--> [set x] :|: l.
Proof. by []. Qed.

Lemma singl_set_eq: forall (A : Type) (x : A), [ x ] <--> [ set x ].
Proof.
  intros A x x'; split; intros H.
  - inv H. reflexivity. now inv H0.
  - inv H. now constructor.
Qed.

Lemma incl_subset {A : Type} (l1 l2 : seq A) :
  incl l1 l2 -> l1 \subset l2.
Proof.
  intros Hi x; eapply Hi.
Qed.

Lemma incl_hd_same {A : Type} (a : A) (l1 l2 : seq A) :
  incl l1 l2 -> incl (a :: l1) (a :: l2).
Proof.
  intros Hin. firstorder.
Qed.
     
Lemma setI_bigcup_assoc {A B} (s1 : set B) (s2 : set A) (s3 : A -> set B) :
  s1 :&: (\bigcup_(x in s2) s3 x) <--> \bigcup_(x in s2) (s1 :&: (s3 x)).
Proof.
  firstorder.
Qed.

Lemma cons_subset {A : Type} (x : A) (l : seq A) (P : set A) :
  P x ->
  l \subset P ->
  (x :: l) \subset P.
Proof.
  intros Px Pl x' Hin. inv Hin; firstorder.
Qed.

Lemma nil_subset {A : Type} (P : set A) :
  [] \subset P.
Proof.
  intros x H; inv H.
Qed.

Lemma imset_union_incl {U T : Type} (s1 s2 : set U) (f : U -> T) :
  f @: (s1 :|: s2) \subset (f @: s1) :|: (f @: s2).
Proof.
  firstorder.
Qed.

Lemma imset_singl_incl {U T : Type} (x : U) (f : U -> T) :
  f @: [set x] \subset [set (f x)].
Proof.
  intros y Hin. destruct Hin as [y' [Hin1 Hin2]].
  inv Hin1. inv Hin2. reflexivity.
Qed.

Lemma imset_set0_incl  {U T : Type} (f : U -> T) :
  f @: set0 \subset set0.
Proof.
  firstorder.
Qed.

Lemma set_eq_set_incl_r {U : Type} (s1 s2 : set U) :
  s1 <--> s2 -> s2 \subset s1.
Proof.
  firstorder.
Qed.

Lemma set_eq_set_incl_l {U : Type} (s1 s2 : set U) :
  s1 <--> s2 -> s1 \subset s2.
Proof.
  firstorder.
Qed.

Lemma rewrite_set_l {U : Type} (s1 s2 : set U) x :
  s1 x ->
  s1 <--> s2 ->
  s2 x.
Proof.
  firstorder.
Qed.

Lemma rewrite_set_r {U : Type} (s1 s2 : set U) x :
  s2 x ->
  s1 <--> s2 ->
  s1 x.
Proof.
  firstorder.
Qed.

Lemma imset_bigcup_incl_l :
  forall {T U V : Type} (f : U -> V) (A : set T) (F : T -> set U),
  f @: (\bigcup_(x in A) F x) \subset \bigcup_(x in A) f @: F x.
Proof.
  firstorder.
Qed.

Lemma in_imset {U T} (f : U -> T) (S : set U) (x : T) :
  (f @: S) x -> exists y, x = f y.
Proof.
  move => [y [H1 H2]]; eauto.
Qed.

Lemma union_lift_subset_compat {A} (s1 s2 : set (option A)) (s3 s4 : set A) :
  s1 \subset lift s3 ->
  s2 \subset lift s4 ->
  (s1 :|: s2) \subset lift (s3 :|: s4).
Proof.
  firstorder.
Qed.

Lemma lift_subset_pres_l {A} (s1 : set (option A)) (s2 s3 : set A) :
  s1 \subset lift s2 ->
  s1 \subset lift (s2 :|: s3).
Proof.
  firstorder.
Qed.

Lemma lift_subset_pres_r {A} (s1 : set (option A)) (s2 s3 : set A) :
  s1 \subset lift s3 ->
  s1 \subset lift (s2 :|: s3).
Proof.
  firstorder.
Qed.


Lemma set_incl_setI_l {A} (s1 s2 s3 : set A) :
  s1 \subset s3 ->
  (s1 :&: s2) \subset s3.
Proof.
  firstorder.
Qed.

Lemma set_incl_setI_r {A} (s1 s2 s3 : set A) :
  s2 \subset s3 ->
  (s1 :&: s2) \subset s3.
Proof.
  firstorder.
Qed.

Lemma set_incl_setU_l {A} (s1 s2 s3 : set A) :
  s1 \subset s3 ->
  s2 \subset s3 ->
  (s1 :|: s2) \subset s3.
Proof.
  firstorder.
Qed.

Lemma bigcup_set_I_l {A B} (s1 s2 : set A) (s3 : set B) (f : A -> set B) :
  \bigcup_(x in s1) (f x) \subset s3 ->
  \bigcup_(x in (s1 :&: s2)) (f x) \subset s3.
Proof.
  firstorder.
Qed.

Lemma bigcup_set_U {A B} (s1 s2 : set A) (s3 : set B) (f : A -> set B) :
  \bigcup_(x in s1) (f x) \subset s3 ->
  \bigcup_(x in s2) (f x) \subset s3 ->
  \bigcup_(x in (s1 :|: s2)) (f x) \subset s3.
Proof.
  firstorder.
Qed.

Lemma bigcup_set0_subset {A B} (s : set B) (f : A -> set B) :
  \bigcup_(x in set0) (f x) \subset s.
Proof.
  firstorder.
Qed.

Lemma bigcup_cons_subset {A B} l (ls : seq A) (f : A -> set B) s :
  f l \subset s ->
  \bigcup_(x in ls) (f x) \subset s ->
  \bigcup_(x in l :: ls) (f x) \subset s. 
Proof.
  intros H1 H2 x [y [Hl Hr]].
  inv Hl.
  - eauto.
  - eapply H2. eexists; split; eauto.
Qed.

Lemma bigcup_nil_subset {A B} (f : A -> set B) s :
  \bigcup_(x in []) (f x) \subset s. 
Proof.
  intros x [y [H1 H2]]. inv H1.
Qed.

Lemma option_subset {A} (s1 : set (option A)) :
  s1 \subset (isSome :&: s1) :|: [set None]. 
Proof.
  intros [x |]; firstorder.
Qed.

Lemma setU_l_subset {U} (s1 s2 s3 : set U) :
  s1 \subset s3 ->
  s2 \subset s3 ->
  (s1 :|: s2) \subset s3.
Proof.
  firstorder.
Qed.

Lemma bigcup_lift_lift_bigcup {T U} (s1 : set T) (f : T -> set U) :
  \bigcup_(x in s1) (lift (f x)) \subset lift (\bigcup_(x in s1) (f x)).
Proof.
  intros x [y [H1 [[z [H2 H3]] | H2]]].
  + inv H3. left; eexists; split; eauto.
    eexists; split; eauto.
  + inv H2; now right. 
Qed.

Lemma lift_subset_compat {U} (s1 s2 : set U) :
  s1 \subset s2 ->
  lift s1 \subset lift s2.
Proof.
  firstorder.
Qed.

Lemma lift_set_eq_compat {U} (s1 s2 : set U) :
  s1 <--> s2 ->
  lift s1 <--> lift s2.
Proof.
  firstorder.
Qed.

Lemma bigcup_setU_r:
  forall (U T : Type) (s : set U) (f g : U -> set T),
    \bigcup_(i in s) (f i :|: g i) <-->
    \bigcup_(i in s) f i :|: \bigcup_(i in s) g i.
Proof.
  firstorder.
Qed.

Lemma lift_bigcup_comm :
  forall (U T : Type) (s : set U) (f : U -> set T),
    inhabited U ->
    lift (\bigcup_(i in [set : U]) (f i)) <-->
    \bigcup_(i in [set : U]) (lift (f i)).
Proof.
  intros U T s f Hin. unfold lift.
  rewrite !bigcup_setU_r -!imset_bigcup.
  rewrite bigcup_const; eauto.
  reflexivity.
Qed.

Lemma bigcap_setU_distr:
  forall (U T : Type) (s1 s2 : set U) (f : U -> set T),
    \bigcap_(i in s1) f i :&: \bigcap_(i in s2) f i <--> \bigcap_(i in s1 :|: s2) f i.
Proof.
  intros. split.
  - intros [ H1 H2 ] x [ H3 | H3 ]; eauto.
  - intros H. split; intros x H3; eapply H.
    now left. now right.
Qed.

Lemma setI_set_incl :
  forall (A : Type) (s1 s2 s3 : set A),
    s1 \subset s2 ->
    s1 \subset s3 ->
    s1 \subset s2 :&: s3.
Proof.
  firstorder.
Qed.

Lemma imset_isSome {A} (s : set A) :
  Some @: s \subset isSome.
Proof.
  intros y [x [Sx H]]. inv H. eauto.
Qed.

Lemma bigcup_cons_subset_r :
  forall (A B : Type) (l : A) (ls : seq A) (f : A -> set B) (s1 s2 : set B),
    s1 \subset f l ->
    s2 \subset \bigcup_(x in ls) f x ->
    s1 :|: s2 \subset \bigcup_(x in (l :: ls)) f x.
Proof.
  intros A B l ls f s1 s2 H1 H2.
  apply setU_l_subset.
  - rewrite bigcup_setU_l bigcup_set1.
    eapply setU_subset_l. eassumption.
  - rewrite bigcup_setU_l bigcup_set1.
    eapply setU_subset_r. eassumption.
Qed.

Lemma bigcup_setI_cons_subset_r :
  forall (A B : Type) (l : A) (ls : seq A) (f : A -> set B) (s1 s2 : set B) (s3 : set A),
    s3 l ->
    s1 \subset f l ->
    s2 \subset \bigcup_(x in ls :&: s3) f x ->
    s1 :|: s2 \subset \bigcup_(x in (l :: ls) :&: s3) f x.
Proof.
  intros A B l ls f s1 s2 s3 H1 H2 H3.
  apply setU_l_subset.
  - intros x Hs1. eexists l; split; eauto.
    split; eauto. left; eauto.
  - intros x Hs1. eapply H3 in Hs1.
    edestruct Hs1 as [x' [[Hs3 Hls] Hin]].
    eexists x'; split; eauto. split; eauto.
    right; eauto.
Qed.

Lemma imset_union_set_eq:
  forall (U T : Type) (s1 s2 : set U) (f : U -> T),
    f @: (s1 :|: s2) <--> f @: s1 :|: f @: s2.
Proof.
  intros U T s1 s2 f.
  firstorder.
Qed.

Lemma imset_bigcup_setI_cons_subset_r :
  forall (A B : Type) (l : A) (ls : seq A) (f : A -> set (option B))
    (s1 s2 : set B) (s3 : set A),
    s3 l ->
    Some @: s1 \subset f l ->
    Some @: s2 \subset \bigcup_(x in ls :&: s3) f x ->
    Some @: (s1 :|: s2) \subset \bigcup_(x in (l :: ls) :&: s3) f x.
Proof.
  intros A B l ls f s1 s2 s3 H1 H2 H3.
  rewrite imset_union_set_eq. apply setU_l_subset.
  - intros x Hs1. eexists l; split; eauto.
    split; eauto. left; eauto.
  - intros x Hs1. eapply H3 in Hs1.
    edestruct Hs1 as [x' [[Hs3 Hls] Hin]].
    eexists x'; split; eauto. split; eauto.
    right; eauto.
Qed.

Lemma imset_set0_subset {A B} (f : A -> B) (s : set B) :
  (f @: set0) \subset s.
Proof.
  firstorder.
Qed.

Lemma setI_set_eq_r {A : Type} (s1 s2 s2' : set A) :
  s2 <--> s2' ->
  (s1 :&: s2) <--> (s1 :&: s2').
Proof.
  intros. rewrite H; reflexivity.
Qed.

Lemma isSome_subset {A : Type} (s1 s2 s1' s2' : set (option A)) :
  isSome :&: s1 \subset isSome :&: s2 ->
  isSome :&: (s1 :|: ([set None] :&: s1')) \subset isSome :&: (s2 :|: ([set None] :&: s2')).
Proof.
  intros Hyp x [H1 H2]. destruct x as [ x | ]; try discriminate.
  split; eauto.
  inv H2. left; eauto.
  eapply Hyp. now split; eauto.
  inv H. now inv H0.
Qed.

Lemma bigcup_nil_setI {A B} (f : A -> set B)
      (l : seq A) s :
  \bigcup_(x in [] :&: s) (f x) \subset
  \bigcup_(x in (l :&: s)) (f x).
Proof.
  intros z [y [[Hin1 _] Hin2]]. inv Hin1.
Qed.

Lemma isSome_set_eq {A} (s : set (option A)) (s' : set A) :
  s \subset (Some @: s') :|: [set None] ->
  Some @: s' \subset s ->
  isSome :&: s <--> Some @: s'.
Proof.
  intros H1 H2 x; split.
  - intros [H3 H4]. destruct x; try discriminate.
    eapply H1 in H4. inv H4; try discriminate.
    eassumption. 
  - intros [y [H3 H4]].
    inv H4. split. now eauto.
    eapply H2.
    eexists; split; eauto.
Qed.

Lemma set_eq_isSome_sound {A} (s : set (option A)) (s' : set A) :
  isSome :&: s <--> Some @: s' ->
  s \subset (Some @: s') :|: [set None].
Proof.
  intros H [x| ] Hin.
  - left. eapply H.
    eexists; eauto.
  - right; reflexivity.
Qed.

Lemma set_eq_isSome_complete {A} (s : set (option A)) (s' : set A) :
  isSome :&: s <--> Some @: s' ->
  Some @: s' \subset s.
Proof.
  intros H. rewrite <- H. firstorder.
Qed.

Definition somes {A} (s : set (option A)) : set A :=
  [set x | Some x \in s].

Lemma somes_subset {A} (s1 s2 : set (option A)) :
  s1 \subset s2 ->
  somes s1 \subset somes s2.
Proof.
  intros Hs a.
  apply Hs.
Qed.

Lemma bigcup_somes {A B} (sA : set A) (s : A -> set (option B)) :
  somes (\bigcup_(a in sA) s a) <--> \bigcup_(a in sA) somes (s a).
Proof.
  intro b; split; intros [a Ha]; eexists a; auto.
Qed.

Instance proper_somes A : Morphisms.Proper (set_eq ==> set_eq) (@somes A).
Proof. firstorder. Qed.

Lemma bigcup_setI {T U} (s1 : set T) (s2 : set U) F :
  \bigcup_(x in s1) (s2 :&: F x) <--> s2 :&: \bigcup_(x in s1) (F x).
Proof. firstorder. Qed.
