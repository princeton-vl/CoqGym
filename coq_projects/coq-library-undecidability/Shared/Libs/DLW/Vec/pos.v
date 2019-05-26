(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import utils.

Set Implicit Arguments.

Inductive pos : nat -> Set :=
  | pos_fst : forall n, pos (S n)
  | pos_nxt : forall n, pos n -> pos (S n).

Arguments pos_fst {n}.
Arguments pos_nxt {n}.

Notation pos0  := (@pos_fst _).
Notation pos1  := (pos_nxt pos0).
Notation pos2  := (pos_nxt pos1).
Notation pos3  := (pos_nxt pos2).
Notation pos4  := (pos_nxt pos3).
Notation pos5  := (pos_nxt pos4).
Notation pos6  := (pos_nxt pos5).
Notation pos7  := (pos_nxt pos6).
Notation pos8  := (pos_nxt pos7).
Notation pos9  := (pos_nxt pos8).
Notation pos10 := (pos_nxt pos9).
Notation pos11 := (pos_nxt pos10).
Notation pos12 := (pos_nxt pos11).
Notation pos13 := (pos_nxt pos12).
Notation pos14 := (pos_nxt pos13).
Notation pos15 := (pos_nxt pos14).
Notation pos16 := (pos_nxt pos15).
Notation pos17 := (pos_nxt pos16).
Notation pos18 := (pos_nxt pos17).
Notation pos19 := (pos_nxt pos18).
Notation pos20 := (pos_nxt pos19).

Definition pos_iso n m : n = m -> pos n -> pos m.
Proof. intros []; auto. Defined.

Section pos_inv.

  Let pos_inv_t n := 
    match n as x return pos x -> Set with 
      | 0   => fun _ => False 
      | S n => fun i => (( i = pos_fst ) + { p | i = pos_nxt p })%type
    end.

  Let pos_inv : forall n p, @pos_inv_t n p.
  Proof.
    intros _ [ | n p ]; simpl; [ left | right ]; auto; exists p; auto.
  Defined.

  Definition pos_O_inv : pos 0 -> False.
  Proof. apply pos_inv. Defined.

  Definition pos_S_inv n (p : pos (S n)) : ( p = pos_fst ) + { q | p = pos_nxt q }.
  Proof. apply (pos_inv p). Defined.

  Definition pos_nxt_inj n (p q : pos n) (H : pos_nxt p = pos_nxt q) : p = q :=
    match H in _ = a return 
       match a as a' in pos m return 
           match m with 
             | 0 => Prop 
             | S n' => pos n' -> Prop 
           end with
         | pos_fst   => fun _  => True 
         | pos_nxt y => fun x' => x' = y 
       end p with 
     | eq_refl => eq_refl
   end.

End pos_inv.

Arguments pos_S_inv {n} p /.

Section pos_invert.

  (* Position inversion, "singleton elimination" free version 
     One problem remains to fully use it ... it is not
     correctly traversed by type checking algorithm
     of fixpoints (structural recursion)
     
     pos_S_inv work better in that respect 
  *)

  Let pos_invert_t n : (pos n -> Type) -> Type :=
    match n with
        0   => fun P => True
      | S n => fun P => (P (pos_fst) * forall p, P (pos_nxt p))%type
    end.

  Let pos_invert n : forall (P : pos n -> Type), pos_invert_t P -> forall p, P p.
  Proof.
    intros P HP; induction p; simpl in HP; apply HP.
  Defined.
  
  Theorem pos_O_invert X : pos 0 -> X.
  Proof.
    apply pos_invert; simpl; trivial.
  Defined.

  Theorem pos_S_invert n P : P (@pos_fst n) -> (forall p, P (pos_nxt p)) -> forall p, P p.
  Proof.
    intros; apply pos_invert; split; auto.
  Defined.
  
End pos_invert.

Arguments pos_S_invert [n] P _ _ p /.

Ltac pos_O_inv p := exfalso; apply (pos_O_inv p).

Ltac pos_S_inv p := 
  let H := fresh in
  let q := fresh
  in  rename p into q; destruct (pos_S_inv q) as [ H | (p & H) ]; subst q.
 
(* 
Ltac pos_O_inv p := apply (@pos_O_invert _ p).
Ltac pos_S_inv x := induction x as [ | x ] using pos_S_invert.
*)

Ltac pos_inv p :=   
  match goal with
    | [ H: pos 0     |- _ ] => match H with p => pos_O_inv p end
    | [ H: pos (S _) |- _ ] => match H with p => pos_S_inv p end
  end.

Tactic Notation "invert" "pos" hyp(H) := pos_inv H; simpl.

Ltac analyse_pos p := 
  match type of p with
    | pos 0     => pos_inv p
    | pos (S _) => pos_inv p; [ | try analyse_pos p ]
  end. 

Tactic Notation "analyse" "pos" hyp(p) := analyse_pos p.

Definition pos_O_any X : pos 0 -> X.
Proof. intro p; invert pos p. Qed.

Fixpoint pos_left n m (p : pos n) : pos (n+m) :=
  match p with
    | pos_fst   => pos_fst
    | pos_nxt p => pos_nxt (pos_left m p)
  end.

Fixpoint pos_right n m : pos m -> pos (n+m) :=
  match n with 
    | 0   => fun x => x
    | S n => fun p => pos_nxt (pos_right n p)
  end.

Definition pos_both n m : pos (n+m) -> pos n + pos m.
Proof.
  induction n as [ | n IHn ]; intros p.
  + right; exact p.
  + simpl in p; pos_inv p.
    * left; apply pos_fst.
    * destruct (IHn p) as [ a | b ].
      - left; apply (pos_nxt a).
      - right; apply b.
Defined.

Definition pos_lr n m : pos n + pos m -> pos (n+m).
Proof.
  intros [ p | p ]; revert p.
  + apply pos_left.
  + apply pos_right.
Defined.

Fact pos_both_left n m p : @pos_both n m (@pos_left n m p) = inl p.
Proof.
  induction p as [ | n p IHp ]; simpl; auto.
  rewrite IHp; auto.
Qed.

Fact pos_both_right n m p : @pos_both n m (@pos_right n m p) = inr p.
Proof.
  revert p; induction n as [ | n IHn]; intros p; simpl; auto.
  rewrite IHn; auto.
Qed.

(** A bijection between pos n + pos m <-> pos (n+m) **)

Fact pos_both_lr n m p : @pos_both n m (pos_lr p) = p.
Proof.
  destruct p as [ p | p ].
  + apply pos_both_left.
  + apply pos_both_right.
Qed.

Fact pos_lr_both n m p : pos_lr (@pos_both n m p) = p.
Proof.
  revert p; induction n as [ | n IHn ]; intros p; auto.
  simpl in p; pos_inv p; simpl; auto.
  specialize (IHn p).
  destruct (pos_both n m p); simpl in *; f_equal; auto.
Qed.

Section pos_left_right_rect.

  Variable (n m : nat) (P : pos (n+m) -> Type).

  Hypothesis (HP1 : forall p, P (pos_left _ p))
             (HP2 : forall p, P (pos_right _ p)).

  Theorem pos_left_right_rect : forall p, P p.
  Proof.
    intros p.
    rewrite <- pos_lr_both.
    generalize (pos_both n m p); clear p; intros [|]; simpl; auto.
  Qed.

End pos_left_right_rect.

Fixpoint pos_list n : list (pos n) :=
  match n with
    | 0   => nil
    | S n => pos0::map pos_nxt (pos_list n) 
  end.

Fact pos_list_prop n p : In p (pos_list n).
Proof.
  induction p as [ | n p Hp ].
  left; auto.
  simpl; right.
  apply in_map_iff.
  exists p; auto.
Qed.

Fact pos_list_length n : length (pos_list n) = n.
Proof.
  induction n; simpl; auto.
  rewrite map_length; f_equal; auto.
Qed.
 
Fact pos_reification X n (R : pos n -> X -> Prop) : (forall p, exists x, R p x) -> exists f, forall p, R p (f p).
Proof.
  revert R; induction n as [ | n IHn ]; intros R HR.
  exists (pos_O_any X); intros p; invert pos p.
  set (R' q x := R (pos_nxt q) x).
  destruct (IHn R') as (f & Hf).
  intros p; apply HR.
  unfold R' in Hf.
  destruct (HR pos_fst) as (x & Hx).
  exists (fun p => match pos_S_inv p with inl _ => x | inr (exist _ q _) => f q end).
  intros p; invert pos p; auto.
Qed.

Fact pos_reif_t X n (R : pos n -> X -> Prop) : (forall p, { x | R p x }) -> { f | forall p, R p (f p) }.
Proof.
  intros H.
  exists (fun p => (proj1_sig (H p))).
  intros; apply (proj2_sig (H p)).
Qed.

Section pos_eq_dec.

  Definition pos_eq_dec n (x y : pos n) : { x = y } + { x <> y }.
  Proof.
    revert n x y.
    induction x as [ x | n x IH ]; intros y; invert pos y.
    left; trivial.
    right; discriminate.
    right; discriminate.
    destruct (IH y) as [ | C ].
    left; subst; trivial.
    right; contradict C; revert C; apply pos_nxt_inj.
  Defined.

End pos_eq_dec.

Section pos_map.

  Definition pos_map m n := pos m -> pos n.
 
  Definition pm_ext_eq m n (r1 r2 : pos_map m n) := forall p, r1 p = r2 p.  

  Definition pm_lift m n (r : pos_map m n) : pos_map (S m) (S n).
  Proof.
    intros p.
    invert pos p.
    apply pos_fst.
    apply pos_nxt, (r p).
  Defined.
  
  Fact pm_lift_fst m n (r : pos_map m n) : pm_lift r pos0 = pos0.
  Proof. auto. Qed.  
  
  Fact pm_lift_nxt m n (r : pos_map m n) p : pm_lift r (pos_nxt p) = pos_nxt (r p).
  Proof. auto. Qed.

  Arguments pm_lift [ m n ] r p.

  Fact pm_lift_ext m n r1 r2 : @pm_ext_eq m n r1 r2 -> pm_ext_eq (pm_lift r1) (pm_lift r2). 
  Proof.
    intros H12 p; unfold pm_lift.
    invert pos p; simpl; auto.
    f_equal; apply H12.
  Qed.

  Definition pm_comp l m n : pos_map l m -> pos_map m n -> pos_map l n.
  Proof.
    intros H1 H2 p.
    exact (H2 (H1 p)).
  Defined. 
 
  Fact pm_comp_lift l m n r s : pm_ext_eq (pm_lift (@pm_comp l m n r s)) (pm_comp (pm_lift r) (pm_lift s)).
  Proof.
    intros p.
    unfold pm_comp, pm_lift; simpl.
    invert pos p; simpl; auto.
  Qed.

  Definition pm_id n : pos_map n n := fun p => p.

End pos_map.

Arguments pm_lift { m n } _ _ /.
Arguments pm_comp [ l m n ] _ _ _ /.
Arguments pm_id : clear implicits.

Section pos_nat.

  Fixpoint pos_nat n (p : pos n) : { i | i < n }.
  Proof.
    refine (match p with 
              | pos_fst   => exist _ 0 _
              | pos_nxt q => exist _ (S (proj1_sig (pos_nat _ q))) _
            end).
    apply lt_O_Sn.
    apply lt_n_S, (proj2_sig (pos_nat _ q)).
  Defined.

  Definition pos2nat n p := proj1_sig (@pos_nat n p).
  
  Fact pos2nat_prop n p : @pos2nat n p < n.
  Proof. apply (proj2_sig (pos_nat p)). Qed.

  Fixpoint nat2pos n : forall x, x < n -> pos n.
  Proof.
     refine (match n as n' return forall x, x < n' -> pos n' with 
              | O   => fun x H => _
              | S i => fun x H => _
            end).
    exfalso; revert H; apply lt_n_O.
    destruct x as [ | x ].
    apply pos_fst.
    apply pos_nxt. 
    apply (nat2pos i x); revert H; apply lt_S_n.
  Defined.

  Definition nat_pos n : { i | i < n } -> pos n.
  Proof. intros (? & H); revert H; apply nat2pos. Defined.

  Arguments pos2nat n !p /.

  Fact pos2nat_inj n (p q : pos n) : pos2nat p = pos2nat q -> p = q.
  Proof.
    revert q.
    induction p as [ n | n p IHp ]; intros q; invert pos q; simpl; auto; try discriminate 1.
    intros H; f_equal; apply IHp; injection H; trivial.
  Qed.

  Fact pos2nat_nat2pos n i (H : i < n) : pos2nat (nat2pos H) = i.
  Proof.
    revert i H;
    induction n as [ | n IHn ]; intros [ | i ] H; simpl; auto; try omega.
    f_equal.
    apply IHn.
  Qed.
  
  Fact nat2pos_pos2nat n p (H : pos2nat p < n) : nat2pos H = p.
  Proof.
    apply pos2nat_inj; rewrite pos2nat_nat2pos; auto.
  Qed.
  
  Fact pos2nat_fst n : pos2nat (@pos_fst n) = 0.
  Proof. auto. Qed.
  
  Fact pos2nat_nxt n p : pos2nat (@pos_nxt n p) = S (pos2nat p).
  Proof. auto. Qed. 

  Fact pos2nat_left n m p : pos2nat (@pos_left n m p) = pos2nat p.
  Proof. induction p; simpl; auto. Qed.

  Fact pos2nat_right n m p : pos2nat (@pos_right n m p) = n+pos2nat p.
  Proof.
    revert m p; induction n as [ | n IHn ]; intros m p; auto.
    simpl pos_right; simpl plus; rewrite pos2nat_nxt; f_equal; auto.
  Qed.

  Fixpoint pos_sub n (p : pos n) { struct p } : forall m, n < m -> pos m.
  Proof.
    destruct p as [ | n p ]; intros [ | m ] Hm.
    exfalso; clear pos_sub; abstract omega.
    apply pos_fst.
    exfalso; clear pos_sub; abstract omega.
    apply pos_nxt.
    apply (pos_sub n p), lt_S_n, Hm.
  Defined.
  
  Fact pos_sub2nat n p m Hm : pos2nat (@pos_sub n p m Hm) = pos2nat p.
  Proof.
    revert m Hm; induction p as [ n | n p IH ]; intros [ | m ] Hm; try omega. 
    simpl; auto.
    simpl pos_sub; repeat rewrite pos2nat_nxt; f_equal; auto.
  Qed.
  
End pos_nat.

Global Opaque pos_nat.

Fact pos_list2nat n : map (@pos2nat n) (pos_list n) = list_an 0 n.
Proof.
  induction n as [ | n IHn ]; simpl; f_equal.
  rewrite <- (map_S_list_an 0), <- IHn.
  do 2 rewrite map_map.
  apply map_ext.
  intros; rewrite pos2nat_nxt; auto.
Qed.

Section pos_prod.
  
  Variable n : nat.
  
  Let ll := flat_map (fun p => map (fun q => (p,q)) (pos_list n)) (pos_list n).
  Let ll_prop p q : In (p,q) ll.
  Proof. 
    apply in_flat_map; exists p; split.
    apply pos_list_prop.
    apply in_map_iff.
    exists q; split; auto.
    apply pos_list_prop.
  Qed.
  
  Definition pos_not_diag := filter (fun c => if pos_eq_dec (fst c) (snd c) then false else true) ll.

  Fact pos_not_diag_spec p q : In (p,q) pos_not_diag <-> p <> q.
  Proof.
    unfold pos_not_diag.
    rewrite filter_In; simpl.
    destruct (pos_eq_dec p q).
    split. 
    intros (_ & ?); discriminate.
    intros []; auto.
    split; try tauto; split; auto.
  Qed.
  
End pos_prod.

