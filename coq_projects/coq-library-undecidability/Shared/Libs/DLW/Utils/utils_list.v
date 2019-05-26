(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Permutation.

Require Import list_focus utils_tac.

Set Implicit Arguments.

Create HintDb length_db.

Tactic Notation "rew" "length" := autorewrite with length_db.
Tactic Notation "rew" "length" "in" hyp(H) := autorewrite with length_db in H.

Infix "~p" := (@Permutation _) (at level 70).

Section length.
   
  Variable X : Type.

  Implicit Type l : list X.

  Fact length_nil : length (@nil X) = 0.
  Proof. auto. Qed.

  Fact length_cons x l : length (x::l) = S (length l).
  Proof. auto. Qed.

End length.

Hint Rewrite length_nil length_cons app_length map_length rev_length : length_db.

Section list_an.

  Fixpoint list_an a n :=
    match n with 
      | 0   => nil
      | S n => a::list_an (S a) n
    end.

  Fact list_an_S a n : list_an a (S n) = a::list_an (S a) n.
  Proof. auto. Qed. 

  Fact list_an_plus a n m : list_an a (n+m) = list_an a n ++ list_an (n+a) m.
  Proof.
    revert a; induction n; intros a; simpl; auto.
    rewrite IHn; do 3 f_equal; omega.
  Qed.

  Fact list_an_length a n : length (list_an a n) = n.
  Proof.
    revert a; induction n; intro; simpl; f_equal; auto.
  Qed.
  
  Fact list_an_spec a n m : In m (list_an a n) <-> a <= m < a+n.
  Proof.
    revert a; induction n as [ | n IHn ]; simpl; intros a; [ | rewrite IHn ]; omega. 
  Qed.

  Fact map_S_list_an a n : map S (list_an a n) = list_an (S a) n.
  Proof. revert a; induction n; simpl; intro; f_equal; auto. Qed.

  Fact list_an_app_inv a n l r : list_an a n = l++r -> l = list_an a (length l) /\ r = list_an (a+length l) (length r).
  Proof.
    revert a l r; induction n as [ | n IHn ]; intros a l r; simpl.
    + destruct l; destruct r; intros; auto; discriminate.
    + destruct l as [ | x l ]; simpl; intros H1.
      * split; auto.
        rewrite <- H1; simpl; rewrite Nat.add_0_r, list_an_length; auto.
      * injection H1; clear H1; intros H1 H0.
        apply IHn in H1; destruct H1; split; f_equal; auto.
        rewrite H1 at 1; f_equal; omega.
  Qed.

End list_an.

Hint Rewrite list_an_length : length_db.

Definition list_fun_inv X (l : list X) (x : X) : { f : nat -> X | l = map f (list_an 0 (length l)) }.
Proof.
  induction l as [ | y l IHl ].
  + exists (fun _ => x); auto.
  + destruct IHl as (f & Hf).
    exists (fun i => match i with 0 => y | S i => f i end); simpl.
    f_equal.
    rewrite Hf, <- map_S_list_an, map_length, list_an_length, map_map; auto.
Qed.

Fact list_upper_bound (l : list nat) : { m | forall x, In x l -> x < m }.
Proof.
  induction l as [ | x l (m & Hm) ].
  + exists 0; simpl; tauto.
  + exists (1+x+m); intros y [ [] | H ]; simpl; try omega.
    generalize (Hm _ H); intros; omega.
Qed.

Section list_injective.

  Variable X : Type.
   
  Definition list_injective (ll : list X) :=  forall l a m b r, ll = l ++ a :: m ++ b :: r -> a <> b.
  
  Fact in_list_injective_0 : list_injective nil.
  Proof. intros [] ? ? ? ? ?; discriminate. Qed.
  
  Fact in_list_injective_1 x ll : ~ In x ll -> list_injective ll -> list_injective (x::ll).
  Proof.
    intros H1 H2 l a m b r H3.
    destruct l as [ | u l ].
    inversion H3; subst.
    destruct m as [ | v m ].
    contradict H1; subst; simpl; auto.
    contradict H1; subst; simpl; right; apply in_or_app; right; left; auto.
    inversion H3; subst.
    apply (H2 l _ m _ r); auto.
  Qed.
  
  Fact list_injective_inv x ll : list_injective (x::ll) -> ~ In x ll /\ list_injective ll.
  Proof.
    split.
    intros H1; apply in_split in H1; destruct H1 as (l & r & ?); subst.
    apply (H nil x l x r); auto.
    intros l a m b r ?; apply (H (x::l) a m b r); subst; solve list eq.
  Qed.
  
  Variable P : list X -> Type.
  
  Hypothesis (HP0 : P nil).
  Hypothesis (HP1 : forall x l, ~ In x l -> P l -> P (x::l)).
  
  Theorem list_injective_rect l : list_injective l -> P l.
  Proof.
    induction l as [ [ | x l ] IHl ] using (measure_rect (@length _)).
    intro; apply HP0.
    intros; apply HP1.
    apply list_injective_inv, H.
    apply IHl; simpl; auto.
    apply list_injective_inv with (1 := H).
  Qed.

End list_injective.

Fact list_injective_map X Y (f : X -> Y) ll :
       (forall x y, f x = f y -> x = y) -> list_injective ll -> list_injective (map f ll).
Proof.
  intros Hf.
  induction 1 as [ | x l Hl IHl ] using list_injective_rect.
  apply in_list_injective_0.
  simpl; apply in_list_injective_1; auto.
  contradict Hl.
  apply in_map_iff in Hl.
  destruct Hl as (y & Hl & ?).
  apply Hf in Hl; subst; auto.
Qed.

Section iter.
  
  Variable (X : Type) (f : X -> X).

  Fixpoint iter x n :=
    match n with
      | 0   => x
      | S n => iter (f x) n
    end.

  Fact iter_plus x a b : iter x (a+b) = iter (iter x a) b.
  Proof. revert x; induction a; intros x; simpl; auto. Qed.

  Fact iter_swap x n : iter (f x) n = f (iter x n).
  Proof. 
    change (iter (f x) n) with (iter x (1+n)).
    rewrite plus_comm, iter_plus; auto.
  Qed.

End iter.

Fixpoint list_repeat X (x : X) n :=
  match n with
    | 0   => nil
    | S n => x::list_repeat x n
  end.
  
Fact list_repeat_plus X x a b : @list_repeat X x (a+b) = list_repeat x a ++ list_repeat x b.
Proof. induction a; simpl; f_equal; auto. Qed.
  
Fact list_repeat_length X x n : length (@list_repeat X x n) = n.
Proof. induction n; simpl; f_equal; auto. Qed.

Fact In_list_repeat X (x y : X) n : In y (list_repeat x n) -> x = y /\ 0 < n.
Proof.
  induction n; simpl; intros [].
  split; auto; omega.
  split; try omega; apply IHn; auto.
Qed.

Fact map_list_repeat X Y f x n : @map X Y f (list_repeat x n) = list_repeat (f x) n.
Proof. induction n; simpl; f_equal; auto. Qed.

Fact map_cst_repeat X Y (y : Y) ll : map (fun _ : X => y) ll = list_repeat y (length ll).
Proof. induction ll; simpl; f_equal; auto. Qed.
  
Fact map_cst_snoc X Y (y : Y) ll mm : y :: map (fun _ : X => y) ll++mm = map (fun _ => y) ll ++ y::mm.
Proof. induction ll; simpl; f_equal; auto. Qed.

Fact map_cst_rev  X Y (y : Y) ll : map (fun _ : X => y) (rev ll) = map (fun _ => y) ll.
Proof. do 2 rewrite map_cst_repeat; rewrite rev_length; auto. Qed.

Fact In_perm X (x : X) l : In x l -> exists m, x::m ~p l.
Proof.
  intros H; apply in_split in H.
  destruct H as (m & k & ?); subst.
  exists (m++k).
  apply Permutation_cons_app; auto.
Qed.

Fact list_app_eq_inv X (l1 l2 r1 r2 : list X) :
       l1++r1 = l2++r2 -> { m | l1++m = l2 /\ r1 = m++r2 } 
                        + { m | l2++m = l1 /\ r2 = m++r1 }.
Proof.
  revert l2 r1 r2; induction l1 as [ | x l1 IH ].
  intros; left; exists l2; auto.
  intros [ | y l2 ] r1 r2; simpl; intros H.
  right; exists (x::l1); auto.
  inversion H.
  destruct (IH l2 r1 r2) as [ (m & Hm) | (m & Hm) ]; auto; 
    [ left | right ]; exists m; split; f_equal; tauto.
Qed.

Fact list_app_cons_eq_inv X (l1 l2 r1 r2 : list X) x :
       l1++r1 = l2++x::r2 -> { m | l1++m = l2 /\ r1 = m++x::r2 } 
                           + { m | l2++x::m = l1 /\ r2 = m++r1 }.
Proof.
  intros H.
  apply list_app_eq_inv in H.
  destruct H as [ H | (m & H1 & H2) ]; auto.
  destruct m as [ | y m ].
  left; exists nil; simpl in *; split; auto.
  revert H1; do 2 rewrite <- app_nil_end; auto.
  inversion H2; subst.
  right; exists m; auto.
Qed.

Fact list_cons_app_cons_eq_inv X (l2 r1 r2 : list X) x y :
       x::r1 = l2++y::r2 -> (l2 = nil /\ x = y /\ r1 = r2) 
                          + { m | l2 = x::m /\ r1 = m++y::r2 }.
Proof.
  intros H.
  destruct l2 as [ | z m ]; simpl in H.
  + left; inversion H; auto.
  + right; exists m; inversion H; auto.
Qed.
 
Fact list_app_inj X (l1 l2 r1 r2 : list X) : length l1 = length l2 -> l1++r1 = l2++r2 -> l1 = l2 /\ r1 = r2.
Proof.
  revert l2; induction l1 as [ | x l1 IH ]; intros [ | y l2 ]; try discriminate.
  simpl; auto.
  intros H1 H2; inversion H1; inversion H2.
  apply IH in H4; auto.
  split; f_equal; tauto.
Qed.

Fact list_split_length X (ll : list X) k : k <= length ll -> { l : _ & { r | ll = l++r /\ length l = k } }.
Proof.
  revert k; induction ll as [ | x ll IHll ]; intros k.
  exists nil, nil; split; simpl in * |- *; auto; omega.
  destruct k as [ | k ]; intros Hk.
  exists nil, (x::ll); simpl; split; auto.
  destruct (IHll k) as (l & r & H1 & H2).
  simpl in Hk; omega.
  exists (x::l), r; split; simpl; auto; f_equal; auto.
Qed.

Fact list_pick X (ll : list X) k : k < length ll -> { x : _ & { l : _ & { r | ll = l++x::r /\ length l = k } } }.
Proof.
  revert k; induction ll as [ | x ll IHll ]; intros k.
  simpl; omega.
  destruct k as [ | k ]; intros H.
  exists x, nil, ll; simpl; auto.
  simpl in H.
  destruct IHll with (k := k) as (y & l & r & ? & ?); try omega.
  exists y, (x::l), r; subst; simpl; split; auto.
Qed.

Fact list_split_middle X l1 (x1 : X) r1 l2 x2 r2 : 
       ~ In x1 l2 -> ~ In x2 l1 -> l1++x1::r1 = l2++x2::r2 -> l1 = l2 /\ x1 = x2 /\ r1 = r2.
Proof.
  intros H1 H2 H.
  apply list_app_eq_inv in H.
  destruct H as [ (m & H3 & H4) | (m & H3 & H4) ]; destruct m.
  inversion H4; subst; rewrite <- app_nil_end; auto.
  inversion H4; subst; destruct H1; apply in_or_app; right; left; auto.
  inversion H4; subst; rewrite <- app_nil_end; auto.
  inversion H4; subst; destruct H2; apply in_or_app; right; left; auto.
Qed.

Section flat_map.

  Variable (X Y : Type) (f : X -> list Y).

  Fact flat_map_app l1 l2 : flat_map f (l1++l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
    induction l1; simpl; auto; solve list eq; f_equal; auto.
  Qed.

  Fact flat_map_app_inv l r1 y r2 : flat_map f l = r1++y::r2 -> exists l1 m1 x m2 l2, l = l1++x::l2 /\ f x = m1++y::m2 
                                                                  /\ r1 = flat_map f l1++m1 /\ r2 = m2++flat_map f l2. 
  Proof.
    revert r1 y r2.
    induction l as [ | x l IHl ]; intros r1 y r2 H.
    + destruct r1; discriminate.
    + simpl in H.
      apply list_app_cons_eq_inv in H.
      destruct H as [ (m & Hm1 & Hm2) | (m & Hm1 & Hm2) ].
      - apply IHl in Hm2.
        destruct Hm2 as (l1 & m1 & x' & m2 & l2 & G1 & G2 & G3 & G4); subst.
        exists (x::l1), m1, x', m2, l2; simpl; repeat (split; auto).
        rewrite app_ass; auto.
      - exists nil, r1, x, m, l; auto.
  Qed.

End flat_map.

Definition prefix X (l ll : list X) := exists r, ll = l++r.
  
Infix "<p" := (@prefix _) (at level 70, no associativity).
  
Section prefix. (* as an inductive predicate *)
   
  Variable X : Type.
  
  Implicit Types (l ll : list X).
  
  Fact in_prefix_0 ll : nil <p ll.
  Proof.
    exists ll; auto.
  Qed.
  
  Fact in_prefix_1 x l ll : l <p ll -> x::l <p x::ll.
  Proof.
    intros (r & ?); subst; exists r; auto.
  Qed.

  Fact prefix_length l m : l <p m -> length l <= length m.
  Proof. intros (? & ?); subst; rew length; omega. Qed.
  
  Fact prefix_app_lft l r1 r2 : r1 <p r2 -> l++r1 <p l++r2.
  Proof.
    intros (a & ?); subst.
    exists a; rewrite app_ass; auto.
  Qed.
  
  Fact prefix_inv x y l ll : x::l <p y::ll -> x = y /\ l <p ll.
  Proof.
    intros (r & Hr).
    inversion Hr; split; auto.
    exists r; auto.
  Qed.
  
  Fact prefix_list_inv l r rr : l++r <p l++rr -> r <p rr.
  Proof.
    induction l as [ | x l IHl ]; simpl; auto.
    intros H; apply prefix_inv, proj2, IHl in H; auto.
  Qed.

  Fact prefix_refl l : l <p l.
  Proof. exists nil; rewrite <- app_nil_end; auto. Qed.

  Fact prefix_trans l1 l2 l3 : l1 <p l2 -> l2 <p l3 -> l1 <p l3.
  Proof. intros (m1 & H1) (m2 & H2); subst; exists (m1++m2); solve list eq. Qed.

  Section prefix_rect.

    Variables (P : list X -> list X -> Type)
              (HP0 : forall ll, P nil ll)
              (HP1 : forall x l ll, l <p ll -> P l ll -> P (x::l) (x::ll)).
              
    Definition prefix_rect l ll : prefix l ll -> P l ll.
    Proof.
      revert l; induction ll as [ | x ll IHll ]; intros l H.
      
      replace l with (nil : list X).
      apply HP0.
      destruct H as (r & Hr).
      destruct l; auto; discriminate.
      
      destruct l as [ | y l ].
      apply HP0.
      apply prefix_inv in H.
      destruct H as (? & E); subst y.
      apply HP1; [ | apply IHll ]; trivial.
    Qed.
   
  End prefix_rect.

  Fact prefix_app_inv l1 l2 r1 r2 : l1++l2 <p r1++r2 -> { l1 <p r1 } + { r1 <p l1 }.
  Proof.
    revert l2 r1 r2; induction l1 as [ | x l1 IH ].
    left; apply in_prefix_0.
    intros l2 [ | y r1 ] r2.
    right; apply in_prefix_0.
    simpl; intros H; apply prefix_inv in H.
    destruct H as (E & H); subst y.
    destruct IH with (1 := H); [ left | right ];
      apply in_prefix_1; auto.
  Qed. 
  
End prefix.

Definition prefix_spec X (l ll : list X) : l <p ll -> { r | ll = l ++ r }.
Proof.
  induction 1 as [ ll | x l ll _ (r & Hr) ] using prefix_rect.
  exists ll; trivial.
  exists r; simpl; f_equal; auto.
Qed.

Fact prefix_app_lft_inv X (l1 l2 m : list X) : l1++l2 <p m -> { m2 | m = l1++m2 /\ l2 <p m2 }.
Proof.
  intros H.
  apply prefix_spec in H. 
  destruct H as (r & H).
  exists (l2++r); simpl.
  solve list eq in H; split; auto.
  exists r; auto.
Qed.

Section list_assoc.

  Variables (X Y : Type) (eq_X_dec : eqdec X).

  Fixpoint list_assoc x l : option Y :=
    match l with 
      | nil  => None
      | (y,a)::l => if eq_X_dec x y then Some a else list_assoc x l
    end.

  Fact list_assoc_eq x y l x' : x = x' -> list_assoc x' ((x,y)::l) = Some y.
  Proof.    
    intros []; simpl.
    destruct (eq_X_dec x x) as [ | [] ]; auto.
  Qed.

  Fact list_assoc_neq x y l x' : x <> x' -> list_assoc x' ((x,y)::l) = list_assoc x' l.
  Proof.    
    intros H; simpl.
    destruct (eq_X_dec x' x) as [ | ]; auto.
    destruct H; auto.
  Qed.

  Fact list_assoc_In x l : 
    match list_assoc x l with 
      | None   => ~ In x (map fst l)
      | Some y => In (x,y) l
    end.
  Proof.
    induction l as  [ | (x',y) l IHl ]; simpl; auto.
    destruct (eq_X_dec x x'); subst; auto.
    destruct (list_assoc x l); auto.
    intros [ ? | ]; subst; tauto.
  Qed.

  Fact In_list_assoc x l : In x (map fst l) -> { y | list_assoc x l = Some y /\ In (x,y) l }.
  Proof.
    intros H.
    generalize (list_assoc_In x l).
    destruct (list_assoc x l) as [ y | ].
    exists y; auto.
    tauto.
  Qed.
  
  Fact not_In_list_assoc x l : ~ In x (map fst l) -> list_assoc x l = None.
  Proof.
    intros H.
    generalize (list_assoc_In x l).
    destruct (list_assoc x l) as [ y | ]; auto.
    intros H1; contradict H.
    apply in_map_iff.
    exists (x,y); simpl; auto.
  Qed.

  Fact list_assoc_app x ll mm : list_assoc x (ll++mm) 
                              = match list_assoc x ll with
                                  | None   => list_assoc x mm
                                  | Some y => Some y
                                end.
  Proof.
    induction ll as [ | (x',?) ]; simpl; auto.
    destruct (eq_X_dec x x'); auto.
  Qed.

End list_assoc.

Section list_first_dec.

  Variable (X : Type) (P : X -> Prop) (Pdec : forall x, { P x } + { ~ P x }).
  
  Theorem list_choose_dec ll : { l : _ & { x : _ & { r | ll = l++x::r /\ P x /\ forall y, In y l -> ~ P y } } }
                             + { forall x, In x ll -> ~ P x }.
  Proof.
    induction ll as [ | a ll IH ];
      [ | destruct (Pdec a) as [ Ha | Ha ]; [ | destruct IH as [ (l & x & r & H1 & H2 & H3) | H ]] ].
    * right; intros _ [].
    * left; exists nil, a, ll; repeat split; auto.
    * left; exists (a::l), x, r; repeat split; subst; auto. 
      intros ? [ | ]; subst; auto.
    * right; intros ? [ | ]; subst; auto.
  Qed.
  
  Theorem list_first_dec a ll : P a -> In a ll -> { l : _ & { x : _ & { r | ll = l++x::r /\ P x /\ forall y, In y l -> ~ P y } } }.
  Proof.
    intros H1 H2.
    destruct (list_choose_dec ll) as [ H | H ]; trivial.
    destruct (H _ H2 H1).
  Qed.
  
End list_first_dec.

Section map.

  Variable (X Y : Type) (f : X -> Y).
  
  Fact map_cons_inv ll y m : map f ll = y::m -> { x : _ & { l | ll = x::l /\ f x = y /\ map f l = m } }.
  Proof.
    destruct ll as [ | x l ]; try discriminate; simpl.
    intros H; inversion H; subst; exists x, l; auto.
  Qed.

  Fact map_app_inv ll m n : map f ll = m++n -> { l : _  & { r | ll = l++r /\ m = map f l /\ n = map f r } }.
  Proof.
    revert m n; induction ll as [ | x ll IH ]; intros m n H.
    * destruct m; destruct n; try discriminate; exists nil, nil; auto.
    * destruct m as [ | y m ]; simpl in H.
      + exists nil, (x::ll); auto.
      + inversion H; subst y.
        destruct IH with (1 := H2) as (l & r & H3 & H4 & H5); subst.
        exists (x::l), r; auto.
  Qed.
  
  Fact map_middle_inv ll m y n : map f ll = m++y::n -> { l : _ & { x : _ & { r | ll = l++x::r /\ map f l = m /\ f x = y /\ map f r = n } } }.
  Proof.
    intros H.
    destruct map_app_inv with (1 := H) as (l & r & H1 & H2 & H3).
    symmetry in H3.
    destruct map_cons_inv with (1 := H3) as (x & r' & H4 & H5 & H6); subst.
    exists l, x, r'; auto.
  Qed.
  
End map.

Fact Forall2_mono X Y (R S : X -> Y -> Prop) :
         (forall x y, R x y -> S x y) -> forall l m, Forall2 R l m -> Forall2 S l m.
Proof.
  induction 2; constructor; auto.
Qed. 

Fact Forall2_nil_inv_l X Y R m : @Forall2 X Y R nil m -> m = nil.
Proof.
  inversion_clear 1; reflexivity.
Qed.

Fact Forall2_nil_inv_r X Y R m : @Forall2 X Y R m nil -> m = nil.
Proof.
  inversion_clear 1; reflexivity.
Qed.

Fact Forall2_cons_inv X Y R x l y m : @Forall2 X Y R (x::l) (y::m) <-> R x y /\ Forall2 R l m.
Proof.
  split.
  inversion_clear 1; auto.
  intros []; constructor; auto.
Qed.

Fact Forall2_app_inv_l X Y R l1 l2 m : 
    @Forall2 X Y R (l1++l2) m -> { m1 : _ & { m2 | Forall2 R l1 m1 /\ Forall2 R l2 m2 /\ m = m1++m2 } }.
Proof.
  revert l2 m;
  induction l1 as [ | x l1 IH ]; simpl; intros l2 m H.
  exists nil, m; repeat split; auto.
  destruct m as [ | y m ].
  apply Forall2_nil_inv_r in H; discriminate H.
  apply Forall2_cons_inv in H; destruct H as [ H1 H2 ].
  apply IH in H2.
  destruct H2 as (m1 & m2 & H2 & H3 & H4); subst m.
  exists (y::m1), m2; repeat split; auto.
Qed.

Fact Forall2_app_inv_r X Y R l m1 m2 : 
    @Forall2 X Y R l (m1++m2) -> { l1 : _ & { l2 | Forall2 R l1 m1 /\ Forall2 R l2 m2 /\ l = l1++l2 } }.
Proof.
  revert m2 l;
  induction m1 as [ | y m1 IH ]; simpl; intros m2 l H.
  exists nil, l; repeat split; auto.
  destruct l as [ | x l ].
  apply Forall2_nil_inv_l in H; discriminate H.
  apply Forall2_cons_inv in H; destruct H as [ H1 H2 ].
  apply IH in H2.
  destruct H2 as (l1 & l2 & H2 & H3 & H4); subst l.
  exists (x::l1), l2; repeat split; auto.
Qed.

Fact Forall2_cons_inv_l X Y R a ll mm : 
      @Forall2 X Y R (a::ll) mm 
   -> { b : _ & { mm' | R a b /\ mm = b::mm' /\ Forall2 R ll mm' } }.
Proof.
  intros H.
  apply Forall2_app_inv_l with (l1 := a::nil) (l2 := ll) in H.
  destruct H as (l & mm' & H1 & H2 & H3).
  destruct l as [ | y l ].
  exfalso; inversion H1.
  apply Forall2_cons_inv in H1.
  destruct H1 as [ H1 H4 ].
  apply Forall2_nil_inv_l in H4; subst l.
  exists y, mm'; auto.
Qed.

Fact Forall2_cons_inv_r X Y R b ll mm : 
      @Forall2 X Y R ll (b::mm) 
   -> { a : _ & { ll' | R a b /\ ll = a::ll' /\ Forall2 R ll' mm } }.
Proof.
  intros H.
  apply Forall2_app_inv_r with (m1 := b::nil) (m2 := mm) in H.
  destruct H as (l & ll' & H1 & H2 & H3).
  destruct l as [ | x l  ].
  exfalso; inversion H1.
  apply Forall2_cons_inv in H1.
  destruct H1 as [ H1 H4 ].
  apply Forall2_nil_inv_r in H4; subst l.
  exists x, ll'; auto.
Qed.

Fact Forall2_map_left X Y Z (R : Y -> X -> Prop) (f : Z -> Y) ll mm : Forall2 R (map f ll) mm <-> Forall2 (fun x y => R (f x) y) ll mm.
Proof.
  split.
  revert mm.
  induction ll; intros [ | y mm ] H; simpl in H; auto; try (inversion H; fail).
  apply Forall2_cons_inv in H; constructor. 
  tauto.
  apply IHll; tauto.
  induction 1; constructor; auto.
Qed.

Fact Forall2_map_right X Y Z (R : Y -> X -> Prop) (f : Z -> X) mm ll : Forall2 R mm (map f ll) <-> Forall2 (fun y x => R y (f x)) mm ll.
Proof.
  split.
  revert mm.
  induction ll; intros [ | y mm ] H; simpl in H; auto; try (inversion H; fail).
  apply Forall2_cons_inv in H; constructor. 
  tauto.
  apply IHll; tauto.
  induction 1; constructor; auto.
Qed.

Fact Forall2_map_both X Y X' Y' (R : X -> Y -> Prop) (f : X' -> X) (g : Y' -> Y) ll mm : Forall2 R (map f ll) (map g mm) <-> Forall2 (fun x y => R (f x) (g y)) ll mm.
Proof.
  rewrite Forall2_map_left, Forall2_map_right; split; auto.
Qed.

Fact Forall2_Forall X (R : X -> X -> Prop) ll : Forall2 R ll ll <-> Forall (fun x => R x x) ll.
Proof.
  split.
  induction ll as [ | x ll ]; inversion_clear 1; auto.
  induction 1; auto.
Qed.

Fact Forall_app X (P : X -> Prop) ll mm : Forall P (ll++mm) <-> Forall P ll /\ Forall P mm.
Proof.
  repeat rewrite Forall_forall.
  split.
  firstorder.
  intros (H1 & H2) x Hx.
  apply in_app_or in Hx; firstorder.
Qed.

Fact Forall_cons_inv X (P : X -> Prop) x ll : Forall P (x::ll) <-> P x /\ Forall P ll.
Proof.
  split.
  + inversion 1; auto.
  + constructor; tauto.
Qed.

Fact Forall_rev X (P : X -> Prop) ll : Forall P ll -> Forall P (rev ll).
Proof.
  induction 1 as [ | x ll Hll IH ].
  constructor.
  simpl.
  apply Forall_app; split; auto.
Qed.

Fact Forall_map X Y (f : X -> Y) (P : Y -> Prop) ll : Forall P (map f ll) <-> Forall (fun x => P (f x)) ll.
Proof.
  split.
  + induction ll; simpl; try rewrite Forall_cons_inv; constructor; tauto.
  + induction 1; simpl; constructor; auto.
Qed.

Fact Forall_forall_map X (f : nat -> X) n l (P : X -> Prop) :
           l = map f (list_an 0 n) -> (forall i, i < n -> P (f i)) <-> Forall P l.
Proof.
  intros Hl; rewrite Forall_forall.
  split.
  + intros H x; rewrite Hl, in_map_iff.
    intros (y & ? & H1).
    apply list_an_spec in H1; subst; apply H; omega.
  + intros H x Hx; apply H; rewrite Hl, in_map_iff.
    exists x; split; auto; apply list_an_spec; omega.
Qed.

Fact Forall_impl X (P Q : X -> Prop) ll : (forall x, In x ll -> P x -> Q x) -> Forall P ll -> Forall Q ll.
Proof.
  intros H; induction 1 as [ | x ll Hx Hll IH ]; constructor.
  + apply H; simpl; auto.
  + apply IH; intros ? ?; apply H; simpl; auto.
Qed.

Fact Forall_filter X (P : X -> Prop) (f : X -> bool) ll : Forall P ll -> Forall P (filter f ll).
Proof. induction 1; simpl; auto; destruct (f x); auto. Qed.


