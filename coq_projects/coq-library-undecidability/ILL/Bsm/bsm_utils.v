(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Bool.

Require Import utils pos vec. 
Require Import subcode sss.
Require Import list_bool tiles_solvable bsm_defs.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).

Section Binary_Stack_Machines.

  Variable (n : nat).

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Section empty_stack.

    Variable (x : pos n) (i : nat).
    
    (* Code for emptying stack x *)

    Definition empty_stack := POP x i (3+i) :: PUSH x Zero :: POP x i i :: nil.

    Fact empty_stack_length : length empty_stack = 3.
    Proof. auto. Qed.

    Fact empty_stack_spec v : (i,empty_stack) // (i,v) ->> (3+i,v[nil/x]).
    Proof.
      set (l := v#>x).
      generalize (eq_refl l).
      unfold l at 2.
      generalize l v; clear l v.
      unfold empty_stack.
      induction l as [ | [] l IHl ]; intros v Hv.

      bsm sss POP empty with x i (3+i).
      bsm sss stop; f_equal.
      apply vec_pos_ext; intros p; dest x p.

      bsm sss POP 1 with x i (3+i) l.
      bsm sss PUSH with x Zero.
      bsm sss POP 0 with x i i l; rew vec.
      clear Hv.
      specialize (IHl (v[l/x])).
      spec in IHl.     
      rew vec.
      revert IHl; rew vec.

      bsm sss POP 0 with x i (3+i) l.
      clear Hv.
      specialize (IHl (v[l/x])).
      spec in IHl.     
      rew vec.
      revert IHl; rew vec.
    Qed.

  End empty_stack.

  Section move_rev.

    Variable (x y : pos n) (Hxy : x <> y) (i : nat).

    Let y' := y.
    
    (* Code that transfers stack x to y, reversing x in the interval *)

    Definition move_rev_stack := 
      (*    i *)   POP x (4+i) (7+i) ::
      (*  1+i *)   PUSH y One  :: PUSH y' Zero :: POP y' i i ::
      (*  4+i *)   PUSH y Zero :: PUSH x  Zero :: POP x i i ::
      (*  7+i *)   nil.

    Fact length_move_rev_stack : length move_rev_stack = 7.
    Proof. auto. Qed. 

    Fact move_rev_stack_spec l v w :
              v#>x = l
           -> w = v[nil/x][(rev l++v#>y)/y] 
           -> (i,move_rev_stack) // (i,v) ->> (7+i,w).
    Proof.
      revert v w; induction l as [ | [] l IHl ]; intros v w Hv Hw; subst w; unfold move_rev_stack.
      * bsm sss POP empty with x (4+i) (7+i).
        bsm sss stop.
        f_equal.
        apply vec_pos_ext; intros z; dest z y; dest z x.
      * bsm sss POP 1 with x (4+i) (7+i) l.
        bsm sss PUSH with y One.
        bsm sss PUSH with y' Zero.
        bsm sss POP 0 with y' i i (One::v#>y); unfold y'; rew vec.
        apply IHl; rew vec.
        apply vec_pos_ext; intros z.
        dest z y; simpl; solve list eq.
        dest z x.
      * bsm sss POP 0 with x (4+i) (7+i) l.
        bsm sss PUSH with y Zero.
        bsm sss PUSH with x Zero.
        bsm sss POP 0 with x i i l; rew vec.
        apply IHl; rew vec.
        apply vec_pos_ext; intros z.
        dest z y; simpl; solve list eq.
        dest z x.
    Qed.

  End move_rev.

  Section copy_rev_stack.

    Variable (x y z : pos n) (Hxy : x <> y) (Hxz : x <> z) (Hyz : y <> z) (i : nat).

    Let y' := y.
    
    (* Code that transfers x to both y and z, reversing x in the interval *)

    Definition copy_rev_stack := 
      (*    i *)   POP x (5+i) (9+i) ::
      (*  1+i *)   PUSH y One  :: PUSH z One  :: PUSH y' Zero :: POP y' i i ::
      (*  5+i *)   PUSH y Zero :: PUSH z Zero :: PUSH x Zero :: POP x i i ::
      (*  9+i *)   nil.

    Fact length_copy_rev_stack : length copy_rev_stack = 9.
    Proof. auto. Qed.

    Fact copy_rev_stack_spec l v w :
              v#>x = l
           -> w = v[nil/x][(rev l++v#>y)/y][(rev l++v#>z)/z]
           -> (i,copy_rev_stack) // (i,v) ->> (9+i,w).
    Proof.
      revert v w; induction l as [ | [] l IHl ]; intros v w Hv Hw; subst w; unfold copy_rev_stack.
      * bsm sss POP empty with x (5+i) (9+i).
        bsm sss stop.
        f_equal.
        apply vec_pos_ext; intros k; dest k z; dest k y; dest k x.
      * bsm sss POP 1 with x (5+i) (9+i) l.
        bsm sss PUSH with y One.
        bsm sss PUSH with z One.
        bsm sss PUSH with y' Zero.
        bsm sss POP 0 with y' i i (One::v#>y); unfold y'; rew vec.
        apply IHl; rew vec.
        apply vec_pos_ext; intros k.
        dest k z; simpl; solve list eq.
        dest k y; dest k x.
      * bsm sss POP 0 with x (5+i) (9+i) l.
        bsm sss PUSH with y Zero.
        bsm sss PUSH with z Zero.
        bsm sss PUSH with x Zero.
        bsm sss POP 0 with x i i l; rew vec.
        apply IHl; rew vec.
        apply vec_pos_ext; intros k.
        dest k z; simpl; solve list eq.
        dest k y; dest k x.
    Qed.

  End copy_rev_stack.

  Hint Rewrite empty_stack_length length_move_rev_stack length_copy_rev_stack : length_db.
  
  Section copy_stack.

    Variable (x y z : pos n) (Hxy : x <> y) (Hxz : x <> z) (Hyz : y <> z) (i : nat).
    
    (* Code that copies x into y, stack z must be an empty spare stack *)

    Definition copy_stack := move_rev_stack x z i ++ copy_rev_stack z x y (7+i).

    Fact copy_stack_length : length copy_stack = 16.
    Proof. auto. Qed.

    Fact copy_stack_spec l v w :
              v#>x = l
           -> v#>z = nil
           -> w = v[(l++v#>y)/y]
           -> (i,copy_stack) // (i,v) ->> (16+i,w).
    Proof.
      intros H1 H2 H3; subst w.
      unfold copy_stack.
      apply sss_compute_trans with (st2 := (7+i,v[nil/x][(rev l)/z])).
      * apply subcode_sss_compute with (P := (i,move_rev_stack x z i)); auto.
        apply move_rev_stack_spec with l; auto.
        rew vec; rewrite H2; solve list eq.
      * apply subcode_sss_compute with (P := (7+i,copy_rev_stack z x y (7+i))); auto.
        apply copy_rev_stack_spec with (rev l); rew vec.
        apply vec_pos_ext; intros k.
        dest k z; simpl; solve list eq.
        dest k y; [ | dest k x ];
        rewrite rev_involutive; auto.
    Qed.

  End copy_stack.

  Hint Rewrite copy_stack_length : length_db.

  Section compare_stacks.

    Variables (x y : pos n) (Hxy : x <> y) (i p q : nat).

    Let x' := x.
    
    (* Code that compares two stacks x and y:
          - ends at p if the stacks x and y are identical
          - ends at q otherwise
       The status of x and y is unspecified after the
       execution but the stacks other than x and y are
       unmodified *)

    Definition compare_stacks :=
      (*   i    *)  POP x (4+i) (7+i) ::
      (* 1+i    *)  POP y q q ::
      (* 2+i    *)  PUSH x Zero :: POP x i i ::
      (* 4+i    *)  POP y i q ::
      (* 5+i    *)  PUSH y Zero :: POP y q i ::
      (* 7+i    *)  POP y q p ::
      (* 8+i    *)  PUSH x' Zero :: POP x' q q :: nil.

    Fact compare_stacks_length : length compare_stacks = 10.
    Proof. auto. Qed.

    Let cs_spec_rec l : forall m v, v#>x = l 
                                 -> v#>y = m 
                                 -> exists w, (forall z, z <> x -> z <> y -> v#>z = w#>z)
                                 /\ (l =  m -> (i,compare_stacks) // (i,v) ->> (p,w))
                                 /\ (l <> m -> (i,compare_stacks) // (i,v) ->> (q,w)).
    Proof.
      induction l as [ | [] l IHl ]; intros [ | [] m ] v Hx Hy; unfold compare_stacks.

      (* l = nil, m = nil *)
   
      exists v; split; auto.
      split; [ intros _ | intros [] ]; auto.
      bsm sss POP empty with x (4+i) (7+i).
      bsm sss POP empty with y q p.
      bsm sss stop.

      (* l = nil, m = One::_ *)
      
      exists (v[m/y]); split.
      intros; rew vec.
      split; [ discriminate | intros _ ].
      bsm sss POP empty with x (4+i) (7+i).
      bsm sss POP 1 with y q p m.
      bsm sss PUSH with x' Zero.
      bsm sss POP 0 with x' q q nil.
      rew vec; f_equal; auto.
      bsm sss stop; f_equal.
      unfold x'; rew vec.
      apply vec_pos_ext; intros z; dest x z.

      (* l = nil, m = Zero::_ *)

      exists (v[m/y]); split.
      intros; rew vec.
      split; [ discriminate | intros _ ].
      bsm sss POP empty with x (4+i) (7+i).
      bsm sss POP 0 with y q p m.
      bsm sss stop.

      (* l = One::_, m = nil *)

      exists (v[l/x]); split.
      intros; rew vec.
      split; [ discriminate | intros _ ].
      bsm sss POP 1 with x (4+i) (7+i) l.
      bsm sss POP empty with y q q; rew vec.
      bsm sss stop.

      (* l = One::l', m = One::m' *)

      destruct (IHl m (v[l/x][m/y])) as (w & H1 & H2 & H3); rew vec.
      exists w; split.
      intros z G1 G2; specialize (H1 _ G1 G2); rewrite <- H1; rew vec.
      split. 

      intros E1; inversion E1 as [ E ]; clear E1.
      specialize (H2 E).
      bsm sss POP 1 with x (4+i) (7+i) l.
      bsm sss POP 1 with y q q m; rew vec.
      bsm sss PUSH with x Zero.
      bsm sss POP 0 with x i i l; rew vec.
      eq goal H2; do 2 f_equal.
      apply vec_pos_ext; intros z; dest z x.

      intros E1.
      spec in H3.
      contradict E1; subst; auto.
      bsm sss POP 1 with x (4+i) (7+i) l.
      bsm sss POP 1 with y q q m; rew vec.
      bsm sss PUSH with x Zero.
      bsm sss POP 0 with x i i l; rew vec.
      eq goal H3; do 2 f_equal.
      apply vec_pos_ext; intros z; dest z x.

      (* l = One::l', m = Zero::m' *)

      exists (v[l/x][m/y]).
      split.
      intros; rew vec.
      split; [ discriminate | intros _ ].
      bsm sss POP 1 with x (4+i) (7+i) l.
      bsm sss POP 0 with y q q m; rew vec.
      bsm sss stop.

      (* l = Zero::l', m = nil *)

      exists (v[l/x]).
      split.
      intros; rew vec.
      split; [ discriminate | intros _ ].
      bsm sss POP 0 with x (4+i) (7+i) l.
      bsm sss POP empty with y i q; rew vec.
      bsm sss stop.

      (* l = Zero::l', m = nil *)

      exists (v[l/x][m/y]).
      split.
      intros; rew vec.
      split; [ discriminate | intros _ ].
      bsm sss POP 0 with x (4+i) (7+i) l.
      bsm sss POP 1 with y i q m; rew vec.
      bsm sss PUSH with y Zero.
      bsm sss POP 0 with y q i m; rew vec.
      bsm sss stop.

      (* l = Zero::l', m = Zero::m' *)

      destruct (IHl m (v[l/x][m/y])) as (w & H1 & H2 & H3); rew vec.
      exists w; split.
      intros z G1 G2; specialize (H1 _ G1 G2); rewrite <- H1; rew vec.
      split. 

      intros E1; inversion E1 as [ E ]; clear E1.
      specialize (H2 E).
      bsm sss POP 0 with x (4+i) (7+i) l.
      bsm sss POP 0 with y i q m; rew vec.

      intros E1.
      spec in H3.
      contradict E1; subst; auto.
      bsm sss POP 0 with x (4+i) (7+i) l.
      bsm sss POP 0 with y i q m; rew vec.
    Qed.

    Fact compare_stack_eq_spec v : 
            v#>x = v#>y 
         ->   exists w, (i,compare_stacks) // (i,v) ->> (p,w) 
           /\ forall z, z <> x -> z <> y -> v#>z = w#>z.
    Proof.
      intros E.
      destruct (cs_spec_rec v eq_refl eq_refl) as (w & H1 & H2 & H3).
      exists w; split; auto.
    Qed.

    Fact compare_stack_neq_spec v : 
            v#>x <> v#>y 
         ->   exists w, (i,compare_stacks) // (i,v) ->> (q,w) 
           /\ forall z, z <> x -> z <> y -> v#>z = w#>z.
    Proof.
      intros E.
      destruct (cs_spec_rec v eq_refl eq_refl) as (w & H1 & H2 & H3).
      exists w; split; auto.
    Qed.

    Theorem compare_stack_spec v : exists j w, (i,compare_stacks) // (i,v) ->> (j,w) 
                                         /\ forall z, z <> x -> z <> y -> v#>z = w#>z
                                         /\ (v#>x = v#>y /\ j = p \/ v#>x <> v#>y /\ j = q).
    Proof.
      destruct (list_bool_dec (v#>x) (v#>y)) as [ H | H ].
      + destruct compare_stack_eq_spec with (1 := H) as (w & H1 & H2); exists p, w; auto.
      + destruct compare_stack_neq_spec with (1 := H) as (w & H1 & H2); exists q, w; auto.
    Qed.

  End compare_stacks.

  Section half_tile.

    Variable (x : pos n).
    
    (* Code that pushes the reverse of a half tile on a stack *)

    Fixpoint half_tile (l : list bool) := 
      match l with
        | nil  => nil
        | b::l => PUSH x b :: half_tile l
      end.

    Fact half_tile_length l : length (half_tile l) = length l.
    Proof. induction l; simpl; f_equal; auto. Qed. 

    Fact half_tile_spec i l v : (i,half_tile l) // (i,v) ->> (length (half_tile l)+i,v[(rev l++v#>x)/x]).
    Proof.
      rewrite half_tile_length.
      revert i v; induction l as [ | b l IHl ]; intros i v; simpl.

      bsm sss stop; f_equal.
      apply vec_pos_ext; intros z; dest z x.

      bsm sss PUSH with x b.
      specialize (IHl (1+i) (v[(b::v#>x)/x])).
      apply subcode_sss_compute with (P := (1+i,half_tile l)).
      subcode_tac; solve list eq.
      eq goal IHl; do 2 f_equal.
      omega.
      apply vec_pos_ext; intros z; dest z x.
      solve list eq.
    Qed.

  End half_tile.

  Hint Rewrite empty_stack_length compare_stacks_length half_tile_length : length_db.

  Section tile.

    Variable (x y : pos n) (Hxy : x <> y) (high low : list bool).
    
    (* Code that pushes a reversed tile on both stacks high and low *)
  
    Definition tile := half_tile x (rev high) ++ half_tile y (rev low).

    Fact tile_length : length tile = length high + length low.
    Proof. unfold tile; rew length; auto. Qed.

    Fact tile_spec i v st : st = (length tile+i,v[(high++v#>x)/x][(low++v#>y)/y]) 
                         -> (i,tile) // (i,v) ->> st.
    Proof.
      intro; subst.
      unfold tile.
      apply sss_compute_trans with (st2 := (length (half_tile x (rev high))+i,v[(high++v#>x)/x])).
      rewrite <- (rev_involutive high) at 3.
      apply subcode_sss_compute with (P := (i,half_tile x (rev high))).
      subcode_tac.
      apply half_tile_spec.
      rewrite <- (rev_involutive low) at 3.
      apply subcode_sss_compute with (P := (length (half_tile x (rev high))+i,half_tile y (rev low))).
      subcode_tac; solve list eq.
      replace (length (half_tile x (rev high) ++ half_tile y (rev low)) + i)
      with    (length (half_tile y (rev low)) + (length (half_tile x (rev high)) + i)).
      replace (v#>y) with (v[(high ++ v#>x)/x]#>y) by rew vec.
      apply half_tile_spec.
      rew length; omega.
    Qed.

  End tile.

  Hint Rewrite tile_length : length_db.
  
  Section transfer_ones.

    Variable (x y : pos n) (Hxy : x <> y) (i p q : nat).
    
    (* Code that does the following:
         * if x is 111110++l where 1 occurs k times then
            - x becomes l
            - y becomes bbbbb++y where b occurs k times
         * if x is 11111 where 1 occurs k times then
            - x becomes nil
            - y becomes bbbbb++y where b occurs k times
     *)

    Definition transfer_ones b := POP x p q :: PUSH y b :: PUSH y Zero :: POP y i i :: nil.

    Fact transfer_ones_length b : length (transfer_ones b) = 4.
    Proof. auto. Qed.

    Fact transfer_ones_spec_1 b k l v st : v#>x = list_repeat One k ++ Zero :: l 
                                    -> st = (p,v[l/x][(list_repeat b k ++ v#>y)/y])
                                    -> (i,transfer_ones b) // (i,v) ->> st.
    Proof.
      intros H1 E; subst st.
      revert v H1.
      induction k as [ | k IHk ]; intros v; intros Hx; 
        simpl list_repeat; simpl app; unfold transfer_ones; simpl in Hx.

      bsm sss POP 0 with x p q l.
      bsm sss stop; f_equal.
      apply vec_pos_ext; intros z; dest z y.

      bsm sss POP 1 with x p q (list_repeat One k ++ Zero :: l).
      bsm sss PUSH with y b.
      bsm sss PUSH with y Zero.
      bsm sss POP 0 with y i i (b::v#>y); rew vec.
      specialize (IHk (v [(list_repeat One k ++ Zero :: l) / x] [(b :: v #> y) / y])).
      spec in IHk.
      rew vec.
      eq goal IHk; do 2 f_equal.
      apply vec_pos_ext; intros z; dest z y.
      2: dest z x. 
      change (b :: list_repeat b k ++ v#>y)
      with (list_repeat b (S k) ++ v#>y).
      replace (S k) with (k+1) by omega.
      rewrite list_repeat_plus; solve list eq.
    Qed.

    Fact transfer_ones_spec_2 b k v st : v#>x = list_repeat One k 
                                    -> st = (q,v[nil/x][(list_repeat b k ++ v#>y)/y])
                                    -> (i,transfer_ones b) // (i,v) ->> st.
    Proof.
      intros H1 E; subst st.
      revert v H1.
      induction k as [ | k IHk ]; intros v; intros Hx; 
        simpl list_repeat; simpl app; unfold transfer_ones; simpl in Hx.

      bsm sss POP empty with x p q.
      bsm sss stop; f_equal.
      apply vec_pos_ext; intros z; dest z y; dest z x.

      bsm sss POP 1 with x p q (list_repeat One k).
      bsm sss PUSH with y b.
      bsm sss PUSH with y Zero.
      bsm sss POP 0 with y i i (b::v#>y); rew vec.
      specialize (IHk (v [(list_repeat One k) / x] [(b :: v #> y) / y])).
      spec in IHk.
      rew vec.
      eq goal IHk; do 2 f_equal.
      apply vec_pos_ext; intros z; dest z y.
      2: dest z x. 
      change (b :: list_repeat b k ++ v#>y)
      with (list_repeat b (S k) ++ v#>y).
      replace (S k) with (k+1) by omega.
      rewrite list_repeat_plus; solve list eq.
    Qed.

  End transfer_ones.

  Hint Rewrite transfer_ones_length : length_db.

  Section increment.

    Variable (x y : pos n) (Hxy : x <> y).
    
    (* Code that increments the stack x by one ie.
       for l such that list_bool_succ x l, x becomes l
       
       y is a spare register which is (globally) unmodified
    *)

    Definition increment i := PUSH y Zero :: transfer_ones x y (1+i)   (5+i) (10+i) One  ++ 
                              PUSH x One  :: transfer_ones y x (6+i)  (15+i) (15+i) Zero ++
                              PUSH x Zero :: transfer_ones y x (11+i) (15+i) (15+i) Zero ++ 
                              nil.

    Fact increment_length i : length (increment i) = 15.
    Proof. unfold increment; rew length; auto. Qed.

    Fact increment_spec_1 i v k l : v#>x = list_repeat One k ++ Zero :: l
                               -> (i,increment i) // (i,v) ->> (15+i,v[(list_repeat Zero k ++ One :: l)/x]).
    Proof.
      intros Hx.
      unfold increment.

      bsm sss PUSH with y Zero.

      apply subcode_sss_compute_trans with (P := (1+i,transfer_ones x y (1+i) (5+i) (10+i) One))
                                           (st2 := (5+i,v[l/x][(list_repeat One k ++ Zero:: v#>y)/y])); auto.
      apply transfer_ones_spec_1 with (k := k) (l := l); rew vec.
      f_equal.
      apply vec_pos_ext; intros z; dest z y; dest z x.

      bsm sss PUSH with x One.
      apply subcode_sss_compute_trans with (P := (6+i,transfer_ones y x (6+i) (15+i) (15+i) Zero))
                                           (st2 := (15+i,v[(list_repeat Zero k++One::l)/x])); auto.
      apply transfer_ones_spec_1 with (k := k) (l := v#>y); rew vec.
      f_equal.
      apply vec_pos_ext; intros z; dest z y; dest z x.
 
      bsm sss stop.
    Qed.

    Fact increment_spec_2 i v k : v#>x = list_repeat One k
                               -> (i,increment i) // (i,v) ->> (15+i,v[(list_repeat Zero (S k))/x]).
    Proof.
      intros Hx.
      unfold increment.

      bsm sss PUSH with y Zero.

      apply subcode_sss_compute_trans with (P := (1+i,transfer_ones x y (1+i) (5+i) (10+i) One))
                                           (st2 := (10+i,v[nil/x][(list_repeat One k ++ Zero:: v#>y)/y])); auto.
      apply transfer_ones_spec_2 with (k := k); rew vec.
      f_equal.
      apply vec_pos_ext; intros z; dest z y; dest z x.

      bsm sss PUSH with x Zero.
      apply subcode_sss_compute_trans with (P := (11+i,transfer_ones y x (11+i) (15+i) (15+i) Zero))
                                           (st2 := (15+i,v[(list_repeat Zero (S k))/x])); auto.
      apply transfer_ones_spec_1 with (k := k) (l := v#>y); rew vec.
      f_equal.
      apply vec_pos_ext; intros z; dest z y; dest z x.
      replace (S k) with (k+1) by omega.
      rewrite list_repeat_plus; auto.
 
      bsm sss stop.
    Qed.

    Fact increment_spec i v l m : 
           list_bool_succ l m 
        -> v#>x = l
        -> (i,increment i) // (i,v) ->> (15+i,v[m/x]).
    Proof.
      revert l m; intros ? ? [ k l | k ] H.
      apply increment_spec_1; auto.
      apply increment_spec_2; auto.
    Qed.

  End increment.

  Hint Rewrite increment_length : length_db.

  Section full_decoder.
  
    Implicit Type (lt : list ((list bool) *  list bool)).

    Definition size_cards lt := fold_right (fun c x => length (fst c) + length (snd c) + x) 0 lt.

    Variables (c h l : pos n) (Hch : c <> h) (Hcl : c <> l) (Hhl : h <> l).
    Variables (p : nat)   (* jumps here when decoding worked correctly *)
              (q : nat)   (* jumps here when decoding produced an error *)
              .

    Let decoder_error := PUSH c Zero :: POP c q q :: nil.
    
    (* Code that implements a decoder for tile indices 
         - ll is a list of tiles (th,tl)
         
         - when c starts with a valid tile index in ll
           encoded as 00001 (with n 0s to represent b)
           then the corresponding tile is stacked into 
           h and l. The code ends up at s
           
         - otherwise, h and l are left unchanged and the
           code ends up at q
     *)

    Fixpoint decoder s i lt :=
      match lt with 
        | nil           => decoder_error
        | (th,tl) :: lt => POP c (3+length (tile h l th tl)+i) q ::
                           tile h l th tl ++
                           PUSH c Zero ::
                           POP c s s ::
                           decoder s (3+length (tile h l th tl)+i) lt 
      end.

    Fixpoint length_decoder lt :=
      match lt with
        | nil => 2
        | (th,tl) :: lt => 3+length th+length tl+length_decoder lt 
      end.
  
    Fact decoder_length s i lt : length (decoder s i lt) = length_decoder lt.
    Proof.
      revert s i; induction lt as [ | (th,tl) lt IHlt ]; intros s i; rew length; auto.
      simpl; rew length; rewrite IHlt; omega.
    Qed.

    Fact length_decoder_size lt : length_decoder lt = 2+3*length lt+size_cards lt.
    Proof. induction lt as [ | [] ]; simpl; auto; omega. Qed.

    Local Fact decoder_spec_rec s i mm ll th tl lr lc v w :
           v#>c  = list_repeat Zero (length ll) ++ One :: lc
        -> mm = ll++(th,tl)::lr
        -> w = (s,v[lc/c][(th++v#>h)/h][(tl++v#>l)/l])
        -> (i,decoder s i mm) // (i,v) ->> w.
    Proof.
      revert i mm th tl lr lc v w.
      induction ll as [ | (t1,t2) ll IHll ]; simpl; intros i mm th tl lr lc v w H1 H2 H3; subst w.

      (* The list ll is empty *)

      subst mm; simpl decoder.
      bsm sss POP 1 with c (S (S (S (length (tile h l th tl) + i)))) q lc.

      apply subcode_sss_compute_trans with (P := (1+i,tile h l th tl))
                                           (st2 := (1+length (tile h l th tl)+i,v[lc/c][(th++v#>h)/h][(tl++v#>l)/l])); auto.
      apply tile_spec; auto.
      f_equal.
      rew length; omega.
      apply vec_pos_ext; intros z; dest z l.
   
      bsm sss PUSH with c Zero.
      bsm sss POP 0 with c s s lc; rew vec.
      bsm sss stop; f_equal.
      apply vec_pos_ext; intros z; dest z c.

      (* The list ll is not empty *)

      subst mm; simpl.
      bsm sss POP 0 with c (S (S (S (length (tile h l t1 t2) + i)))) q (list_repeat Zero (length ll) ++ One :: lc).
      apply subcode_sss_compute with (P := (3+length (tile h l t1 t2)+i, 
                                            decoder s (S (S (S (length (tile h l t1 t2)+i)))) (ll++(th,tl)::lr))); auto.
      subcode_tac; solve list eq.
      apply IHll with th tl lr lc; auto.
      rew vec.
      f_equal.
      apply vec_pos_ext; intros z; dest z c.
    Qed.

    Fact decoder_spec_ok s i ll th tl lr lc v st :
           v#>c = list_repeat Zero (length ll) ++ One :: lc
        -> st = (s,v[lc/c][(th++v#>h)/h][(tl++v#>l)/l])
        -> (i,decoder s i (ll++(th,tl)::lr)) // (i,v) ->> st.
    Proof.
      intros; subst; apply decoder_spec_rec with ll th tl lr lc; auto.
    Qed.

    (* There is no trailing 1 *)

    Fact decoder_spec_nok_1 s i ll v k : 
           v#>c = list_repeat Zero k
        -> exists r, (i,decoder s i ll) // (i,v) ->> (q,v[(list_repeat Zero r)/c]).
    Proof.
      revert i v k.
      induction ll as [ | (t1,t2) ll IHll ]; intros i v k H1.

      simpl; unfold decoder_error.
      exists k.
      bsm sss PUSH with c Zero.
      bsm sss POP 0 with c q q (v#>c); rew vec.
      bsm sss stop.
      f_equal.
      apply vec_pos_ext; intros z; dest z c.

      unfold decoder; fold decoder.
      destruct k as [ | k ].

      exists 0.
      bsm sss POP empty with c (3 + length (tile h l t1 t2) + i) q.
      bsm sss stop.
      f_equal; apply vec_pos_ext; intros z; dest z c.

      simpl in H1.
      destruct (IHll (3 + length (tile h l t1 t2) + i) (v[(list_repeat Zero k)/c]) k)
        as (r & Hr); rew vec.
      exists r.
      bsm sss POP 0 with c (3 + length (tile h l t1 t2) + i) q (list_repeat Zero k).
      revert Hr; rew vec; apply subcode_sss_compute; auto.
      subcode_tac; solve list eq.
    Qed.

    (* There might be a trailing 1 but the list of 0s is too long *)

    Fact decoder_spec_nok_2 s i ll lc v k : 
           v#>c = list_repeat Zero k ++ lc
        -> length ll <= k
        -> exists r, (i,decoder s i ll) // (i,v) ->> (q,v[(list_repeat Zero r ++ lc)/c]).
    Proof.
      revert i lc v k.
      induction ll as [ | (t1,t2) ll IHll ]; intros i lc v k H1 H2.

      simpl; unfold decoder_error.
      exists k.
      bsm sss PUSH with c Zero.
      bsm sss POP 0 with c q q (v#>c); rew vec.
      bsm sss stop.
      f_equal.
      apply vec_pos_ext; intros z; dest z c.

      unfold decoder; fold decoder.
      destruct k as [ | k ].

      simpl in H2; omega.

      simpl in H1, H2.
      destruct (IHll (3 + length (tile h l t1 t2) + i) lc (v[(list_repeat Zero k++lc)/c]) k)
        as (r & Hr); rew vec.
      omega.
      exists r.
      bsm sss POP 0 with c (3 + length (tile h l t1 t2) + i) q (list_repeat Zero k++lc).
      revert Hr; rew vec; apply subcode_sss_compute; auto.
      subcode_tac; solve list eq.
    Qed.
    
    (* A full decoder of a list of boolean into a list a valid tile indices,
       stacking the tiles in h/l in the list on the run. 
       
       The following list of indices [5,3,0,2] is encoded as 000001 0001 1 001
       A valid list of booleans is an encoding of [n1,...,n_p] where each
       n_i is stricly less than length mm 
       
       If the encoding on the list of indices is incorrect in any way:
         - either not a list of indices
         - or some index is to big
       then the full decoder ends up at q.
       
       The empty list is not a valid list of tile indices 
       
     *)

    Definition full_decoder i ll :=
         POP c (4+i) p ::
         PUSH c One ::
         PUSH h Zero ::
         POP h (5+i) q ::
         PUSH c Zero ::
         decoder i (5+i) ll.

    Definition length_full_decoder ll := 5 + length_decoder ll.
    
    Fact full_decoder_length i ll : length (full_decoder i ll) = length_full_decoder ll.
    Proof. unfold full_decoder, length_full_decoder; rew length; rewrite decoder_length; auto. Qed.

    Local Fact full_dec_start_spec_0 i lt v :
        v#>c = nil
     -> (i,full_decoder i lt) // (i,v) ->> (p,v).
    Proof.
      intros H1.
      unfold full_decoder; simpl in H1.
      bsm sss POP empty with c (4+i) p.
      bsm sss stop; f_equal.
    Qed.

    Local Fact full_dec_start_spec_1 i lt v :
        v#>c <> nil
     -> (i,full_decoder i lt) // (i,v) ->> (5+i,v).
    Proof.
      intros H1.
      case_eq (v#>c).
      intros; destruct H1; auto.
      clear H1.
      unfold full_decoder.
      intros [] lc Hlc.

      bsm sss POP 1 with c (4+i) p lc.
      bsm sss PUSH with c One.
      bsm sss PUSH with h Zero.
      bsm sss POP 0 with h (5+i) q (v#>h); rew vec.
      bsm sss stop; f_equal.
      apply vec_pos_ext; intros z; dest z h; dest z c.

      bsm sss POP 0 with c (4+i) p lc.
      bsm sss PUSH with c Zero.
      bsm sss stop; f_equal.
      apply vec_pos_ext; intros z; dest z c.
    Qed.
 
    Local Fact full_dec_spec_rec i ln lc lt v :
        v#>c = list_nat_bool ln ++ lc
     -> Forall (fun x => x < length lt) ln
     -> let (hh,ll) := tile_concat ln lt
     in (i,full_decoder i lt) // (i,v) ->> (i,v[lc/c][(hh++v#>h)/h][(ll++v#>l)/l]).
    Proof.
      intros H1 H2; revert H2 v H1.
      induction 1 as [ | k ln Hk Hln IHln ]; intros v H1; simpl.

      bsm sss stop; f_equal.
      apply vec_pos_ext; intros z; dest z l; dest z h; dest z c.

      destruct (nth_split _ (nil,nil) Hk) as (ll & lr & H2 & H3).
      revert H2; generalize (nth k lt (nil,nil)); intros (th, tl) H2.
      simpl in H1.
      specialize (IHln (v[(list_nat_bool ln ++ lc)/c][(th++v#>h)/h][(tl++v#>l)/l])).
      spec in IHln; rew vec.
      destruct (tile_concat ln lt) as (thh,tll).
      
      apply sss_compute_trans with (st2 := (5+i,v)).
      apply full_dec_start_spec_1.
      rewrite H1; destruct k; discriminate.
     
      unfold full_decoder.
      apply subcode_sss_compute_trans with (P := (5+i,decoder i (5 + i) lt)) 
           (st2 := (i,v[(list_nat_bool ln++lc)/c][(th++v#>h)/h][(tl++v#>l)/l])); auto.
      subcode_tac; solve list eq.
      subst lt; apply decoder_spec_ok with (list_nat_bool ln++lc); auto.
      rewrite H3; revert H1; solve list eq.

      eq goal IHln; do 2 f_equal.
      apply vec_pos_ext; intros z. 
      dest z l; solve list eq.
      dest z h; solve list eq.
      dest z c.
    Qed.

    (* Correctness lemma for the full decoder when
       then input actually encodes a valid list of tiles *)

    Theorem full_decoder_ok_spec i ln lt v :
        v#>c = list_nat_bool ln
     -> v#>h = nil
     -> v#>l = nil
     -> Forall (fun x => x < length lt) ln
     -> let (hh,ll) := tile_concat ln lt
     in (i,full_decoder i lt) // (i,v) ->> (p,v[nil/c][hh/h][ll/l]).
    Proof.
      intros H1 H2 H3 H4.
      rewrite app_nil_end in H1.
      generalize (@full_dec_spec_rec i ln nil lt v H1 H4).
      destruct (tile_concat ln lt) as (hh,ll).
      intros E.
      apply sss_compute_trans with (1 := E); auto.
      rewrite H2, H3; repeat rewrite <- app_nil_end.
      apply full_dec_start_spec_0; rew vec.
    Qed.
 
    Local Fact full_dec_spec_rec1 i ln lc lt v :
        v#>c = list_nat_bool ln ++ lc
     -> Exists (fun x => length lt <= x) ln
     -> exists w, (i,full_decoder i lt) // (i,v) ->> (q,w)
               /\ forall z, z <> c -> z <> h -> z <> l -> v#>z = w#>z.
    Proof.
      intros H1 H2; revert H2 v H1.
      induction ln as [ | x ln IHln ]; intros Hln v H1.
      inversion Hln.

      generalize (full_dec_start_spec_1 i lt v).
      intros H2; spec in H2.
      rewrite H1; simpl; destruct x; discriminate.
      simpl in H1.
      destruct (le_lt_dec (length lt) x) as [ Hx | Hx ].

      unfold full_decoder.
      solve list eq in H1.
      destruct (decoder_spec_nok_2 i (5+i) lt _ _ H1 Hx) as (r & Hr).
      exists (v [(list_repeat Zero r++One::list_nat_bool ln++lc)/c]); split.
      apply sss_compute_trans with (1 := H2); auto.
      unfold full_decoder; revert Hr; apply subcode_sss_compute; auto.
      subcode_tac; solve list eq.
      intros; rew vec.

      apply Exists_cons in Hln.
      destruct Hln as [ Hln | Hln ].
      omega.
      specialize (IHln Hln).
      destruct (nth_split _ (nil,nil) Hx) as (ll & lr & H3 & H4).
      revert H3; generalize (nth x lt (nil,nil)); intros (th, tl) H3.
      specialize (IHln (v[(list_nat_bool ln++lc)/c][(th++v#>h)/h][(tl++v#>l)/l])).
      spec in IHln; rew vec.
      destruct IHln as (w & Hw & Hw1).
      exists w; split.
      apply sss_compute_trans with (2 := Hw).
      apply sss_compute_trans with (1 := H2); auto.
      rewrite <- H4 in H1.
      solve list eq in H1.
      generalize (@decoder_spec_ok i (5+i) ll th tl lr _ _ _ H1 eq_refl).
      unfold full_decoder; apply subcode_sss_compute.
      subst; subcode_tac; solve list eq.
      intros z G1 G2 G3; generalize (Hw1 _ G1 G2 G3); rew vec.
    Qed.

    Local Fact full_dec_spec_rec2 i k lt v :
        v#>c = list_repeat Zero (S k)
     -> exists w, (i,full_decoder i lt) // (i,v) ->> (q,w)
               /\ forall z, z <> c -> z <> h -> z <> l -> v#>z = w#>z.
    Proof.
      intros H.
      destruct (@decoder_spec_nok_1 i (5+i) lt _ _ H) as (r & Hr).
      exists (v[(list_repeat Zero r)/c]); split.
      2: intros; rew vec.
      generalize (@full_dec_start_spec_1 i lt v); intros H1.
      spec in H1.
      rewrite H; discriminate.
      apply sss_compute_trans with (1 := H1); auto.
      revert Hr.
      unfold full_decoder.
      apply subcode_sss_compute; auto.
      subcode_tac; solve list eq.
    Qed.
    
    (* Correctness lemma for the full decoder when
       then input encodes an invalid list of tiles *)

    Theorem full_decoder_ko_spec i ln lc lt v :
         v#>c = list_nat_bool ln ++ lc
     -> (Exists (fun x => length lt <= x) ln
     \/  Forall (fun x => x < length lt) ln 
      /\ exists k, lc = list_repeat Zero (S k))
     ->  exists w, (i,full_decoder i lt) // (i,v) ->> (q,w)
               /\ forall z, z <> c -> z <> h -> z <> l -> v#>z = w#>z.
    Proof.
      intros H1 [ H2 | (H2 & k & H3) ].
      apply full_dec_spec_rec1 with ln lc; auto.
      generalize (@full_dec_spec_rec i ln lc lt v H1 H2).
      destruct (tile_concat ln lt) as (hh,ll); intros H4.
      destruct (@full_dec_spec_rec2 i k lt 
           (v[lc/c][(hh++v#>h)/h][(ll++v#>l)/l])) as (w & Hw1 & Hw2); rew vec.
      exists w; split.
      apply sss_compute_trans with (1 := H4); auto.
      intros x E1 E2 E3; rewrite <- Hw2; auto; rew vec.
    Qed.

  End full_decoder.

  Hint Rewrite full_decoder_length : length_db.

  Section simulator.

    Variables (s a h l : pos n) (Hsa : s <> a) (Hsh : s <> h) (Hsl : s <> l)
                                (Hah : a <> h) (Hal : a <> l) (Hhl : h <> l)
              (lt : list ((list bool)*list bool)).

    Section increment_erase.
      
      Variable (i p : nat).
      
      (* This code does the following 
         - increments s (as a list of booleans)
         - empties h, l and a
         - jumps to p
       *)

      Definition increment_erase :=
      (*      i *) increment s a i ++
      (*   15+i *) empty_stack h (15+i) ++
      (*   18+i *) empty_stack l (18+i) ++
      (*   21+i *) empty_stack a (21+i) ++
      (*   24+i *) PUSH l Zero :: POP l p p :: nil.

      Fact increment_erase_length : length increment_erase = 26.
      Proof. auto. Qed.

      Fact increment_erase_spec v ln mn w :
           list_bool_succ ln mn
        -> v#>s = ln 
        -> w = v[mn/s][nil/h][nil/l][nil/a]
        -> (i,increment_erase) // (i,v) ->> (p,w).
      Proof.
        intros H1 H2 ?; subst w.
        unfold increment_erase.

        apply sss_compute_trans with (st2 := (15+i,v[mn/s])).
        apply subcode_sss_compute with (P := (i,increment s a i )); auto.
        apply increment_spec with ln; auto.

        apply sss_compute_trans with (st2 := (18+i,v[mn/s][nil/h])).
        apply subcode_sss_compute with (P := (15+i,empty_stack h (15+i))); auto.
        apply empty_stack_spec.

        apply sss_compute_trans with (st2 := (21+i,v[mn/s][nil/h][nil/l])).
        apply subcode_sss_compute with (P := (18+i,empty_stack l (18+i))); auto.
        apply empty_stack_spec.
        
        apply sss_compute_trans with (st2 := (24+i,v[mn/s][nil/h][nil/l][nil/a])).
        apply subcode_sss_compute with (P := (21+i,empty_stack a (21+i))); auto.
        apply empty_stack_spec.

        bsm sss PUSH with l Zero.
        bsm sss POP 0 with l p p nil; rew vec.
        bsm sss stop.
        f_equal.
        apply vec_pos_ext; intros x; dest x l.
      Qed.

    End increment_erase.

    Hint Rewrite increment_erase_length : length_db.
    
    Section main_init.
      
      Variable (i : nat).
      
      (* Self explaining code:
          - s becomes Zero::nil
          - a, h and l are emptied 
       *)

      Definition main_init :=
      (*      i *) empty_stack s i ++
      (*    3+i *) empty_stack a (3+i) ++
      (*    6+i *) empty_stack h (6+i) ++
      (*    9+i *) empty_stack l (9+i) ++
      (*   12+i *) PUSH s Zero :: nil.

      Fact main_init_length : length main_init = 13.
      Proof. auto. Qed.

      Fact main_init_spec v : (i,main_init) // (i,v) ->> (13+i,v[(Zero::nil)/s][nil/a][nil/h][nil/l]).
      Proof.
        unfold main_init.
        apply subcode_sss_compute_trans with (2 := empty_stack_spec s _ _); auto.
        apply subcode_sss_compute_trans with (2 := empty_stack_spec a _ _); auto.
        apply subcode_sss_compute_trans with (2 := empty_stack_spec h (6+i) _); auto.
        apply subcode_sss_compute_trans with (2 := empty_stack_spec l (9+i) _); auto.
        bsm sss PUSH with s Zero.
        bsm sss stop.
        f_equal.
        apply vec_pos_ext; intros x.
        dest x a; dest x l; dest x h; dest x s.
      Qed.
 
    End main_init.

    Section main_loop.

      Variables (i p : nat).

      Let lFD := length_full_decoder lt.

      (* This code does the following:
           - copies s to a (temporarily using the empty h stack)
           - decodes a as a list of tiles into h/l
             * if the list is correct and h = l at the ends, we
               have a solution to PCP and we jump to p
             * if the list is incorrect, increments s, 
               clean up of h, l and a and start over (loop)
       *)

      Definition main_loop := 
      (*          i *) copy_stack s a h i ++
      (*       16+i *) full_decoder a h l (lFD+16+i) (lFD+26+i) (16+i) lt ++
      (*   lFD+16+i *) compare_stacks h l (lFD+16+i) p (lFD+26+i) ++
      (*   lFD+26+i *) increment_erase (lFD+26+i) i.

      Definition length_main_loop := 52 + lFD.

      Fact main_loop_length : length main_loop = length_main_loop.
      Proof. unfold main_loop, length_main_loop, lFD; rew length; omega. Qed.

      Fact main_loop_size : length_main_loop = 59+3*length lt+size_cards lt.
      Proof.
        unfold length_main_loop, lFD, length_full_decoder.
        rewrite length_decoder_size; omega.
      Qed.

      Fact main_loop_ok_spec v ln :
             v#>h = nil
          -> v#>l = nil
          -> v#>a = nil
          -> v#>s = list_nat_bool ln 
          -> Forall (fun x => x < length lt) ln
          -> (let (hh,ll) := tile_concat ln lt in hh = ll)
          -> exists w, (i,main_loop) // (i,v) ->> (p,w)
                    /\ forall x, x <> a -> x <> h -> x <> l -> v#>x = w#> x.
      Proof.
        intros H0 H1 H2 H3 H4 H5.
        case_eq (tile_concat ln lt).
        intros hh ll E; rewrite E in H5.
        destruct (compare_stack_eq_spec Hhl (lFD+16+i) p (lFD+26+i) (v[nil/a][hh/h][ll/l]))
          as (w & Hw1 & Hw2); rew vec.
        exists w; split.
        unfold main_loop.

        apply sss_compute_trans with (st2 := (16+i,v[(list_nat_bool ln)/a])).
        apply subcode_sss_compute with (P := (i,copy_stack s a h i)); auto.
        apply copy_stack_spec with (list_nat_bool ln); auto.
        rewrite H2, <- app_nil_end; auto.

        apply sss_compute_trans with (st2 := (lFD+16+i,v[nil/a][hh/h][ll/l])).
        apply subcode_sss_compute with (P := (16+i,full_decoder a h l (lFD+16+i) (lFD+26+i) (16+i) lt)); auto.
        generalize (@full_decoder_ok_spec _ _ _ Hah Hal Hhl (lFD+16+i) (lFD+26+i) (16+i) ln lt
          (v[(list_nat_bool ln)/a])); intros H6.
        do 3 (spec in H6; [ rew vec | ]).
        spec in H6; auto.
        rewrite E in H6.
        eq goal H6; do 2 f_equal; rew vec.

        apply subcode_sss_compute with (P := (lFD+16+i,compare_stacks h l (lFD+16+i) p (lFD+26+i))); auto.

        intros x E1 E2 E3; generalize (Hw2 _ E2 E3); rew vec.
      Qed.

      Fact main_loop_ko_spec v ln lc :
             v#>h = nil
          -> v#>l = nil
          -> v#>a = nil
          -> v#>s = list_nat_bool ln ++ lc
          -> (  (   Exists (fun x => length lt <= x) ln
                \/  Forall (fun x => x < length lt) ln /\ exists k, lc = list_repeat Zero (S k) )
             \/  Forall (fun x => x < length lt) ln /\ lc = nil 
                 /\ let (hh,ll) := tile_concat ln lt in hh <> ll)
          -> (i,main_loop) // (i,v) ->> (i,v[(list_bool_next (v#>s))/s]). 
      Proof.
        intros H0 H1 H2 H3 [ H4 | (H4 & ? & H5) ].
        
        destruct (@full_decoder_ko_spec _ _ _ Hah Hal Hhl (lFD+16+i) (lFD+26+i) (16+i)) 
          with (v := v[(list_nat_bool ln ++ lc)/a]) (2 := H4) as (w & Hw1 & Hw2); rew vec.

        unfold main_loop. 
        apply sss_compute_trans with (st2 := (16+i,v[(list_nat_bool ln++lc)/a])).
        apply subcode_sss_compute with (P := (i,copy_stack s a h i)); auto.
        apply copy_stack_spec with (list_nat_bool ln++lc); auto.
        rewrite H2, <- app_nil_end; auto.

        apply subcode_sss_compute_trans with (2 := Hw1); auto. 

        apply subcode_sss_compute with (P := (lFD+26+i,increment_erase (lFD + 26 + i) i)); auto.
        apply increment_erase_spec with (1 := list_bool_next_spec (v#>s)); auto.
        rewrite <- Hw2; auto; rew vec.
        apply vec_pos_ext; intros x.
        dest x a; dest x l; dest x h; dest x s.
        rewrite <- Hw2; auto; rew vec.
        
        unfold main_loop.
        subst lc.
        rewrite <- app_nil_end in H3.
        case_eq (tile_concat ln lt).
        intros hh ll E; rewrite E in H5.
        destruct (compare_stack_neq_spec Hhl (lFD+16+i) p (lFD+26+i) (v[nil/a][hh/h][ll/l]))
          as (w & Hw1 & Hw2); rew vec.

        apply sss_compute_trans with (st2 := (16+i,v[(list_nat_bool ln)/a])).
        apply subcode_sss_compute with (P := (i,copy_stack s a h i)); auto.
        apply copy_stack_spec with (list_nat_bool ln); auto.
        rewrite H2, <- app_nil_end; auto.

        apply sss_compute_trans with (st2 := (lFD+16+i,v[nil/a][hh/h][ll/l])).
        apply subcode_sss_compute with (P := (16+i,full_decoder a h l (lFD+16+i) (lFD+26+i) (16+i) lt)); auto.
        generalize (@full_decoder_ok_spec _ _ _ Hah Hal Hhl (lFD+16+i) (lFD+26+i) (16+i) ln lt
          (v[(list_nat_bool ln)/a])); intros H6.
        do 3 (spec in H6; [ rew vec | ]).
        spec in H6; auto.
        rewrite E in H6.
        eq goal H6; do 2 f_equal; rew vec.
        
        apply sss_compute_trans with (st2 := (lFD+26+i,w)).
        apply subcode_sss_compute with (P := (lFD+16+i,compare_stacks h l (lFD+16+i) p (lFD+26+i))); auto.
 
        apply subcode_sss_compute with (P := (lFD+26+i,increment_erase (lFD + 26 + i) i)); auto.
        apply increment_erase_spec with (1 := list_bool_next_spec (v#>s)); auto.
        rewrite <- Hw2; auto; rew vec.
        apply vec_pos_ext; intros x.
        dest x a; dest x l; dest x h; dest x s.
        rewrite <- Hw2; auto; rew vec.
      Qed.

      Implicit Type (v : vec (list bool) n).
      
      Let pre v := v#>h = nil /\ v#>l = nil /\ v#>a = nil.
      Let spec v w := forall x, x <> a -> x <> h -> x <> l -> v#>x = w#> x.
      Let f v := v[(list_bool_next (v#>s))/s].

      Let Hf v : v <> f v.
      Proof.
        intros E.
        apply (list_bool_succ_neq) with (1 := list_bool_next_spec (v#>s)).
        rewrite E at 1.
        unfold f; rew vec.
      Qed.

      Let C2 v := exists ln, 
             v#>s = list_nat_bool ln 
          /\ Forall (fun x => x < length lt) ln
          /\ (let (hh,ll) := tile_concat ln lt in hh = ll).

      Let C1 v :=  exists ln lc,
             v#>s = list_nat_bool ln ++ lc
          /\ (  (   Exists (fun x => length lt <= x) ln
                \/  Forall (fun x => x < length lt) ln /\ exists k, lc = list_repeat Zero (S k) )
             \/  Forall (fun x => x < length lt) ln /\ lc = nil 
                 /\ let (hh,ll) := tile_concat ln lt in hh <> ll).

      Let HC v : pre v -> { C1 v } + { C2 v }.
      Proof.
        unfold C1, C2.
        intros _.
        generalize (v#>s); clear v; intros m.
        destruct (list_bool_valid_dec (length lt) m)
          as [ (ln & H1) | (ln & H1) ].
        case_eq (tile_concat ln lt); intros hh ll H2.
        destruct (list_bool_dec hh ll) as [ H3 | H3 ].
        * right.
          exists ln.
          destruct H1 as (H1 & H4).
          rewrite H2; auto.
        * left.
          destruct H1 as (H1 & H4).
          exists ln, nil.
          rewrite <- app_nil_end.
          split; auto.
          right.
          rewrite H2; auto.
        * left.
          destruct H1 as (lc & H1 & H2).
          exists ln, lc; split; auto.
      Qed.

      Hypothesis (Hp : out_code p (i,main_loop)).

      Let HP1 : forall x, pre x -> C1 x -> (i,main_loop) // (i,x) ->> (i,f x) /\ pre (f x).
      Proof.
        intros v (H1 & H2 & H3) (ln & lc & H4 & H5).
        split.
        apply main_loop_ko_spec with ln lc; auto.
        red; unfold f; rew vec; auto.
      Qed.

      Let HP2 : forall x, pre x -> C2 x -> exists y, (i,main_loop) // (i,x) ->> (p,y) /\ spec x y.
      Proof.
        intros v (H1 & H2 & H3) (ln & H4 & H5 & H6).
        apply  main_loop_ok_spec with ln; auto.
      Qed.

      Let main_loop_sound_rec v :
                pre v
             -> (exists n, C2 (iter f v n)) 
             -> exists n w, (i,main_loop) // (i,v) ->> (p,w) /\ spec (iter f v n) w.
      Proof.
        apply sss_loop_sound with (C1 := C1); auto.
      Qed.

      Let main_loop_complete_rec v w q : pre v 
                                      -> out_code q (i,main_loop) 
                                      -> (i,main_loop) // (i,v) ->> (q,w) 
                                      -> p = q /\ exists n, C2 (iter f v n) /\ spec (iter f v n) w.
      Proof.
        apply sss_loop_complete with (C1 := C1); auto.
        apply bsm_sss_fun.
      Qed.

      Let iter_f_v v k : iter f v k = v[(iter list_bool_next (v#>s) k)/s].
      Proof.
        revert v.
        unfold f; induction k as [ | k IHk ]; intros v; simpl; [ | rewrite IHk ]; rew vec.
      Qed.

      Let C2_eq v : v#>s = Zero::nil -> (exists n, C2 (iter f v n)) <-> tiles_solvable lt.
      Proof.
        unfold tiles_solvable.
        intros H1; simpl.
        split.

        intros (k & Hk).
        rewrite iter_f_v, H1 in Hk.
        destruct Hk as (ln & H2 & H3 & H4).
        revert H2; rew vec; intros H2.
        exists ln; repeat split; auto.
        intros E.
        subst ln.
        simpl in H2.
        apply iter_list_bool_next_nil in H2.
        destruct H2; discriminate.

        intros (ln & H2 & H3 & H4).
        destruct (@list_bool_next_total (list_nat_bool ln)) as (k & Hk).
        destruct ln as [ | [ | u ] ln ]; simpl; auto; discriminate.
        exists k.
        rewrite iter_f_v, H1, <- Hk.
        exists ln; rew vec; auto.
      Qed.

      Theorem main_loop_sound v :
          v#>s = Zero::nil -> v#>h = nil -> v#>l = nil -> v#>a = nil
       -> tiles_solvable lt
       -> exists w, (i,main_loop) // (i,v) ->> (p,w) 
                 /\ forall x, x <> s -> x <> a -> x <> h -> x <> l -> v#>x = w#>x.
      Proof.
        intros H1 H2 H3 H4.
        rewrite <- (C2_eq _ H1); auto.
        intros H5.
        destruct main_loop_sound_rec with (2 := H5)
          as (k & w & Hw1 & Hw2).
        red; auto.
        exists w; split; auto.
        unfold spec in Hw2 |- *.
        intros; rewrite <- Hw2; auto.
        rewrite iter_f_v; rew vec.
      Qed.

      Theorem main_loop_complete v w q : 
          v#>s = Zero::nil -> v#>h = nil -> v#>l = nil -> v#>a = nil
       -> out_code q (i,main_loop)
       -> (i,main_loop) // (i,v) ->> (q,w) 
       -> p = q 
       /\ (forall x, x <> s -> x <> a -> x <> h -> x <> l -> v#>x = w#>x)
       /\ tiles_solvable lt.
      Proof.
        intros H1 H2 H3 H4 H5 H6.
        rewrite  <- (C2_eq _ H1); auto.
        destruct main_loop_complete_rec with (2 := H5) (3 := H6)
          as (G1 & k & G2 & G3).
        red; auto.
        split; auto.
        split; [ | exists k ]; auto.
        red in G3.
        intros; rewrite <- G3; auto.
        rewrite iter_f_v; rew vec.
      Qed.

    End main_loop.
    
  End simulator.
    
End Binary_Stack_Machines.
