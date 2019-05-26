(** * Decidability and Enumerability *)

Require Export Shared.Prelim.


(* ** Definitions *)

Definition compl X p := fun x : X => ~ p x.
Definition decidable {X} (p : X -> Prop) := exists f, forall x, p x <-> f x = true.
Definition enumerable {X} (p : X -> Prop) := exists f, forall x, p x <-> exists n : nat, f n = Some x.

Definition discrete X := decidable (fun '(x,y) => x = y :> X). 
Definition enumerable__T X := exists f : nat -> option X, forall x, exists n, f n = Some x.

(* *** more practical type-theoretic characterisations *)

Lemma dec_decidable' X p :
  (forall x : X, dec (p x)) -> { f : _ | forall x, p x <-> f x = true}.
Proof.
  intros d. exists (fun x => if d x then true else false). intros x. destruct (d x); firstorder congruence.
Qed.

Lemma decidable_iff X p :
  decidable p <-> inhabited (forall x : X, dec (p x)).
Proof.
  split.
  - intros [f]. econstructor. intros x. specialize (H x). destruct (f x); firstorder congruence.
  - intros [d]. eapply dec_decidable' in d as [f]. now exists f.
Qed.

Lemma discrete_iff X :
  discrete X <-> inhabited (eq_dec X).
Proof.
  split.
  - intros [] % decidable_iff. econstructor. intros x y; destruct (X0 (x,y)); firstorder.
  - intros [d]. eapply decidable_iff. econstructor. intros (x,y). eapply d.
Qed.

(* ** Facts *)

Lemma dec_compl X p :
  decidable p -> decidable (fun x : X => ~ p x).
Proof.
  intros [f]. exists (fun x => negb (f x)).
  intros. rewrite H. destruct (f x); split; cbn; congruence.
Qed.

Lemma dec_conj X p q :
  decidable p -> decidable q -> decidable (fun x : X => p x /\ q x).
Proof.
  intros [f] [g]. exists (fun x => f x && g x).
  intros. rewrite H, H0. destruct (f x), (g x); cbn; firstorder congruence.
Qed.

Lemma dec_disj X p q :
  decidable p -> decidable q -> decidable (fun x : X => p x \/ q x).
Proof.
  intros [f] [g]. exists (fun x => f x || g x).
  intros. rewrite H, H0. destruct (f x), (g x); cbn; firstorder congruence.
Qed.

Theorem dec_count_enum X (p : X -> Prop) :
  decidable p -> enumerable__T X -> enumerable p.
Proof.
  intros [d Hd] [c Hc].
  exists (fun n => match c n with Some x => if d x then Some x else None | None => None end).
  setoid_rewrite Hd. intros x. split; intros.
  - destruct (Hc x) as [n Hn]. exists n. now rewrite Hn, H.
  - destruct H as [n H]. destruct (c n) eqn:E.
    + destruct (d x0) eqn:E2; now inv H.
    + inv H.
Qed.

Theorem dec_count_enum' X (p : X -> Prop) :
  decidable p -> enumerable__T X -> enumerable (fun x => ~ p x).
Proof.
  intros ? % dec_compl ?. eapply dec_count_enum; eauto.
Qed.

(** ** Closure of enumerable types *)

Lemma enumerable_enumerable_T X :
  enumerable (fun _ : X => True) <-> enumerable__T X.
Proof.
  split.
  - intros [e He]. exists e. intros x. now eapply He.
  - intros [c Hc]. exists c. intros x. split; eauto.
Qed.

Definition cumulative {X} (L: nat -> list X) :=
  forall n, exists A, L (S n) = L n ++ A.
Hint Extern 0 (cumulative _) => intros ?; cbn; eauto.

Lemma cum_ge {X} (L: nat -> list X) n m :
  cumulative L -> m >= n -> exists A, L m = L n ++ A.
Proof.
  induction 2 as [|m _ IH].
  - exists nil. now rewrite app_nil_r.
  - destruct (H m) as (A&->), IH as [B ->].
    exists (B ++ A). now rewrite app_assoc.
Qed.

Lemma cum_ge' {X} (L: nat -> list X) x n m :
  cumulative L -> x el L n -> m >= n -> x el L m.
Proof.
  intros ? H [A ->] % (cum_ge (L := L)). apply in_app_iff. eauto. eauto.
Qed.

Definition enum {X} p (L: nat -> list X) :=
  cumulative L /\ forall x, p x <-> exists m, x el L m.

Section enumerable_enum.

  Variable X : Type.
  Variable p : X -> Prop.
  Variables (e : nat -> option X).
  
  Definition T_ (n : nat) : list X :=  match e n with Some x => [x] | None => [] end.

  Lemma count_enum' : exists L : nat -> list X, forall x, (exists n, e n = Some x) <-> (exists n, x el L n).
  Proof.
    exists T_. split; intros [n H].
    - exists n. unfold T_. rewrite H. eauto.
    - unfold T_ in *. destruct (e n) eqn:E. inv H. eauto. inv H0. inv H.
  Qed.
      
End enumerable_enum.

Lemma enum_to_cumulative X (p : X -> Prop) L :
  (forall x, p x <-> exists m : nat, x el L m) -> exists L, enum p L.
Proof.
  intros H. exists (fix L' n := match n with 0 => [] | S n => L' n ++ L n end).
  split.
  - eauto.
  - intros x. rewrite H. split; intros [m Hm].
    + exists (S m). eauto.
    + induction m; try now inv Hm.
      eapply in_app_iff in Hm as []; eauto.
Qed.    

(** ** Enumerability of pairs of natural numbers *)

Class enumT X :=
  {
    L_T :> nat -> list X;
    cum_T : cumulative L_T ;
    el_T : forall x, exists m, x el L_T m
  }.

Arguments L_T {_ _} _, _ {_} _.
Hint Immediate cum_T.

Lemma discrete_bool : discrete bool.
Proof.
  eapply discrete_iff. econstructor. exact _.
Qed.

Lemma discrete_nat : discrete nat.
Proof.
  eapply discrete_iff. econstructor. exact _.
Qed.

Lemma discrete_nat_nat : discrete (nat * nat).
Proof.
  eapply discrete_iff. econstructor. exact _.
Qed.

Instance enum_bool : enumT bool.
Proof.
  exists (fun n => [true; false]).
  - eauto.
  - intros b; exists 1; destruct b; cbn; eauto.
Qed.

Lemma count_bool :
  enumerable__T bool.
Proof.
  exists (fun n => match n with 0 => Some true | _ => Some false end).
  intros []. now exists 0. now exists 1.
Qed.

Instance enumT_nat : enumT nat.
Proof.
  exists (fix f n := match n with 0 => [0] | S n => f n ++ [S n] end).
  - intros ?; cbn; eauto.
  - intros n. exists n. destruct n; eauto.
Defined.

Lemma count_nat :
  enumerable__T nat.
Proof.
  exists Some. intros n. now exists n.
Qed.

Lemma T_nat_in n m : m <= n -> m el L_T nat n.
Proof.
  induction 1.
  - destruct m; cbn. tauto. apply in_app_iff. cbn. tauto. 
  - cbn. apply in_app_iff. now left.
Qed.

Lemma T_nat_length n : length (L_T nat n) = S n.
Proof.
  induction n; cbn; try rewrite app_length. omega. cbn in *. omega. 
Qed.

Section enumerable_prod.

  Variable X Y : Type.

  Section fixLs.
    
    Variables (L_X : enumT X).
    Variables (L_Y : enumT Y).
    
    Fixpoint T_prod (n : nat) : list (X * Y) :=
      match n
      with
      | 0 => [ (x,y) | (x,y) ∈ (L_T X 0 × L_T Y 0) ]
      | S n => T_prod n ++ [ (x,y) | (x,y) ∈ (L_T X n  × L_T Y n) ]
      end.

    Lemma T_prod_cum : cumulative T_prod.
    Proof.
      intros ?; cbn; eauto.
    Qed.

  End fixLs.
  
  Lemma T_prod_el LX LY (a : X * Y)  :
    exists n, a el T_prod LX LY n.
  Proof.
    destruct a. destruct (el_T x) as [m1], (el_T y) as [m2].
    exists (1 + m1 + m2). cbn. in_app 2.
    in_collect (x,y); eapply cum_ge'; eauto; omega.
  Qed.

  Global Instance prod_enumerable (LX : enumT X) (LY : enumT Y) : enumT (X * Y). 
  Proof.
    exists (T_prod LX LY).
    - apply T_prod_cum.
    - apply T_prod_el.
  Defined.

End enumerable_prod.

Lemma C_exhaustive n m : (n,m) el L_T (1 + n + m).
Proof.
  cbn. in_app 2. in_collect (n, m); apply T_nat_in; omega.  
Qed.

Lemma C_longenough n : length (L_T (nat * nat) n) > n.
Proof.
  induction n; cbn.
  - omega.
  - rewrite app_length, map_length, prod_length, T_nat_length. cbn in *. remember (n + n * S n) as k. omega.
Qed.

Definition R_nat_nat n : option (nat * nat) := nthe n (L_T n).

Lemma pairs_retract :  forall p, exists n, R_nat_nat n = Some p. 
Proof.
  intros [n m].  
  unfold R_nat_nat. destruct(pos (fun x y => Dec (x = y)) (n,m) (L_T (1 + n + m))) as [ k | ] eqn:A.
  exists k. destruct (nthe k (L_T k)) eqn:B.
  - eapply pos_nthe in A.
    destruct (le_lt_dec k (1 + n + m)) as [D | ?].
    + destruct (cum_ge (@cum_T (nat * nat) _) D) as [B' HB]. rewrite HB in A.
      rewrite (nthe_app_l _ B) in A. now injection A.
    + assert (1 + n + m <= k) as D by omega.
      destruct (cum_ge (@cum_T (nat * nat) _) D) as [B' HB]. rewrite HB in B.
      rewrite (nthe_app_l  _ A) in B. now injection B.
  - exfalso. edestruct nthe_length. 2:{ rewrite e in B. inv B. } eapply C_longenough.
  - exfalso. destruct (el_pos (fun x y => Dec (x = y)) (C_exhaustive n m)) as [k H]. congruence.
Qed.

Lemma enumerable_nat_nat : enumerable__T (nat * nat).
Proof.
  exists R_nat_nat. eapply pairs_retract.
Qed.
  
Section enum_enumerable.
  
  Context X L p { enum_X : @enum X p L }.

  Definition ofNat n := match R_nat_nat n with Some (n, m) => nthe n ((L m)) | None => None end.

  Lemma enum_count : enumerable p.
  Proof.
    exists ofNat. unfold R_nat_nat. destruct enum_X as [CX HX].
    intros. rewrite HX.
    - split; intros [n].
      + eapply In_nth_error in H as [m].
        destruct (pairs_retract (m, n)) as [k]. exists k. unfold ofNat. now rewrite H0.
      + unfold ofNat in *. destruct R_nat_nat as [ [] | ].
        eapply nth_error_In in H. eauto. inv H.
  Qed.
  
End enum_enumerable.

(** ** Discrete types are closed under ... *)

Lemma discrete_prod X Y : discrete X -> discrete Y -> discrete (X * Y).
Proof.
  intros [d1] % discrete_iff [d2] % discrete_iff.
  eapply discrete_iff. eauto.
Qed.

Lemma discrete_sum X Y : discrete X -> discrete Y -> discrete (X + Y).
Proof.
  intros [d1] % discrete_iff [d2] % discrete_iff.
  eapply discrete_iff. eauto.
Qed.


Lemma discrete_option X : discrete X -> discrete (option X).
Proof.
  intros [d1] % discrete_iff. eapply discrete_iff. eauto.
Qed.

Lemma discrete_list X : discrete X -> discrete (list X).
Proof.
  intros [d1] % discrete_iff. eapply discrete_iff. eauto.
Qed.

(** ** Enumerable types are closed under ... *)

Lemma enumerable_enum X p :
  (exists L, enum p L) <-> @enumerable X p.
Proof.
  split.
  - intros [L]. eapply enum_count; eauto.
  - intros [f]. destruct count_enum' with (e := f) as (L & ?).
    eapply enum_to_cumulative. intros. now rewrite <- H0, H.
Qed.

Lemma enum_enumT X :
  enumerable__T X <-> inhabited (enumT X).
Proof.
  rewrite <- enumerable_enumerable_T, <-  enumerable_enum. split. 
  - intros [L [] ]. econstructor. unshelve econstructor. exact L. all: firstorder.
  - intros [ [] ]. exists L_T0. firstorder.
Qed.

Lemma enumerable__T_prod X Y : enumerable__T X -> enumerable__T Y -> enumerable__T (X * Y).
Proof.
  intros [LX] % enum_enumT [LY] % enum_enumT.
  eapply enum_enumT. econstructor.
  exact _.  
Qed.

Lemma enumerable__T_sum X Y : enumerable__T X -> enumerable__T Y -> enumerable__T (X + Y).
Proof.
  intros [LX] % enum_enumT [LY] % enum_enumT.
  eapply enum_enumT. econstructor.
  exists (fix f n := match n with 0 => [] | S n => f n ++ [ inl x | x ∈ L_T X n ] ++ [inr y | y ∈ L_T Y n] end).
  - eauto.
  - intros [].
    + destruct (el_T x) as [m]. exists (1 + m).
      cbn. in_app 2. in_collect x. eauto.
    + destruct (el_T y) as [m]. exists (1 + m).
      cbn. in_app 3. in_collect y. eauto.
Qed.

Lemma enumerable__T_option X : enumerable__T X -> enumerable__T (option X).
Proof.
  intros [f]. exists (fun n => match n with 0 => Some None | S n => Some (f n) end).
  intros [].
  - destruct (H x) as [n]. exists (S n). congruence.
  - now exists 0.
Qed.

Section enumerable_list.

  Variable X : Type.

  Section fixL.
    
    Variables (LX : enumT X).

    Fixpoint T_list (n : nat) : list (list X) :=
      match n
      with
      | 0 => [ [] ]
      | S n => T_list n ++ [ x :: L | (x,L) ∈ (L_T X n × T_list n) ]
      end.

    Lemma T_list_cum : cumulative T_list. 
    Proof.
      intros ?; cbn; eauto. 
    Qed.

  End fixL.

  Lemma T_list_el LX l :
    exists n, l el T_list LX n.
  Proof.
    induction l.
    - exists 0. cbn. eauto.
    - destruct IHl as [n IH].
      destruct (el_T a) as [m ?].
      exists (1 + n + m). cbn. intros. in_app 2.
      in_collect (a,l).
      all: eapply cum_ge'; eauto using T_list_cum; omega. 
  Qed.
  
  Global Instance enumerable_list (LX : enumT X) : enumT (list X).
  Proof.
    exists (T_list LX). apply T_list_cum. apply T_list_el.
  Qed.

End enumerable_list.

Lemma enumerable__T_list X : enumerable__T X -> enumerable__T (list X).
Proof.
  intros [LX] % enum_enumT. eapply enum_enumT. econstructor.
  exact _.
Qed.

(** ** Enumerable predicates are closed under ... *)

Lemma enumerable_disj X (p q : X -> Prop) :
  enumerable p -> enumerable q -> enumerable (fun x => p x \/ q x).
Proof.
  intros [Lp] % enumerable_enum [Lq] % enumerable_enum.
  eapply enumerable_enum.
  exists (fix f n := match n with 0 => [] | S n => f n ++ [ x | x ∈ Lp n] ++ [ y | y ∈ Lq n] end).
  econstructor.
  - eauto.
  - intros. split.
    + intros [].
      * eapply H in H1 as [m]. exists (1 + m). cbn. in_app 2. in_collect x. eauto.
      * eapply H0 in H1 as [m]. exists (1 + m). cbn. in_app 3. in_collect x. eauto.
    + intros [m]. induction m.
      * inv H1.
      * inv_collect; firstorder.
Qed.  

Lemma enumerable_conj X (p q : X -> Prop) :
  discrete X -> enumerable p -> enumerable q -> enumerable (fun x => p x /\ q x).
Proof.
  intros [] % discrete_iff [Lp] % enumerable_enum [Lq] % enumerable_enum.
  eapply enumerable_enum.
  exists (fix f n := match n with 0 => [] | S n => f n ++ [ x | x ∈ Lp n, x el Lq n] end).
  econstructor.
  - eauto.
  - intros. split.
    + intros []. eapply H in H1 as [m1]. eapply H0 in H2 as [m2].
      exists (1 + m1 + m2). cbn. in_app 2. in_collect x.
      eapply cum_ge'; eauto. firstorder. omega.
      eapply cum_ge'; eauto. firstorder. omega.
    + intros [m]. induction m.
      * inv H1.
      * inv_collect; firstorder.
Qed.

Lemma projection X Y (p : X * Y -> Prop) :
  enumerable p -> enumerable (fun x => exists y, p (x,y)).
Proof.
  intros [f].
  exists (fun n => match f n with Some (x, y) => Some x | None => None end).
  intros; split.
  - intros [y ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
  - intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inv H0.
    exists y. eapply H. eauto.
Qed.

Lemma projection' X Y (p : X * Y -> Prop) :
  enumerable p -> enumerable (fun y => exists x, p (x,y)).
Proof.
  intros [f].
  exists (fun n => match f n with Some (x, y) => Some y | None => None end).
  intros y; split.
  - intros [x ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
  - intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inv H0.
    exists x. eapply H. eauto.
Qed.
