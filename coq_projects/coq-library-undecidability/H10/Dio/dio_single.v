(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Single Diophantine equations *)

Require Import List Arith Omega Nat.

Require Import utils_tac utils_list sums pos vec. 
Require Import dio_logic dio_elem.

Set Implicit Arguments.

Local Notation "∑" := (msum plus 0).

Section convexity.

  Let convex_1 x p : 2*(x*(x+p)) <= x*x+(x+p)*(x+p).
  Proof.
    rewrite mult_assoc.
    repeat rewrite Nat.mul_add_distr_r.
    repeat rewrite Nat.mul_add_distr_l.
    rewrite (mult_comm p x).
    repeat rewrite <- mult_assoc.
    generalize (x*x) (x*p) (p*p); intros; omega.
  Qed.

  Let convex_2 x p : 2*(x*(x+p)) = x*x+(x+p)*(x+p) -> p = 0.
  Proof.
    rewrite mult_assoc.
    intros H.
    cut (p*p = 0).
    { destruct p; simpl; auto; discriminate. }
    revert H.
    repeat rewrite Nat.mul_add_distr_r.
    repeat rewrite Nat.mul_add_distr_l.
    rewrite (mult_comm p x).
    repeat rewrite <- mult_assoc.
    generalize (x*x) (x*p) (p*p); intros; omega.
  Qed.

  Fact convex_le x y : 2*(x*y) <= x*x+y*y.
  Proof.
    destruct (le_lt_dec x y).
    + replace y with (x+(y-x)) by omega.
      apply convex_1.
    + rewrite (mult_comm x y), plus_comm.
      replace x with (y+(x-y)) by omega.
      apply convex_1.
  Qed.

  Fact convex_eq x y : 2*(x*y) = x*x+y*y -> x = y.
  Proof.
    destruct (le_lt_dec x y).
    + replace y with (x+(y-x)) by omega.
      intros H; apply convex_2 in H; omega.
    + rewrite (mult_comm x y), plus_comm.
      replace x with (y+(x-y)) by omega.
      intros H; apply convex_2 in H; omega.
  Qed.

  Let convex_3 a t x y : 0 < t -> a*x+(a+t)*y = a*y+(a+t)*x -> x = y.
  Proof.
    intros H.
    repeat rewrite Nat.mul_add_distr_r.
    intros H1.
    apply Nat.mul_cancel_l with t; omega.
  Qed.
   
  Fact convex_neq a b x y : a < b -> a*x+b*y = a*y+b*x -> x = y.
  Proof.
    intros H.
    replace b with (a+(b-a)) by omega.
    apply convex_3; omega.
  Qed.

  Hint Resolve convex_le.

  Fact convex_n_le n (f g : nat -> nat) :  ∑ n (fun i => 2*(f i*g i)) 
                                        <= ∑ n (fun i => f i*f i + g i*g i).
  Proof.
    revert f g; induction n as [ | n IHn ]; intros f g.
    + rewrite msum_0; auto.
    + do 2 rewrite msum_S.
      apply plus_le_compat; auto.
  Qed.

  Hint Resolve convex_n_le.

  Let nat_le_sum a b c d : a <= b -> c <= d -> a+c = b+d -> a = b /\ c = d.
  Proof. intros; omega. Qed.


  (* This one can be used to encode a list of equations
     x1 = y1 ... xn = yn into a single equation of size
     linear in n if all the xi, yi have a bounded size 

     Hence one can transform a system elementary diophantine
     equations into a single polynomial equation of linear
     size !! *)

  Fact convex_n_eq n (f g : nat -> nat) : ∑ n (fun i => 2*(f i*g i)) 
                                        = ∑ n (fun i => f i*f i + g i*g i)
                                    <-> forall i, i < n -> f i = g i.
  Proof.
    split.
    + revert f g; induction n as [ | n IHn ]; intros f g.
      * intros; omega.
      * do 2 rewrite msum_S; intros H.
        apply nat_le_sum in H; auto.
        destruct H as (H1 & H2).
        apply convex_eq in H1.
        specialize (IHn _ _ H2).
        intros [ | ] ?; auto; apply IHn; omega.
    + intros Hfg.
      apply msum_ext.
      intros i Hi; rewrite Hfg; auto; ring.
  Qed.

End convexity.

Section diophantine_polynomial.

  Variable (V P : Set).

  Inductive dio_polynomial : Set :=
    | dp_nat : nat -> dio_polynomial                  (* natural number constant *)
    | dp_var : V   -> dio_polynomial                  (* existentially quantified variable *)
    | dp_par : P   -> dio_polynomial                  (* parameter *)
    | dp_comp : dio_op -> dio_polynomial -> dio_polynomial -> dio_polynomial.

  Notation dp_add := (dp_comp do_add).
  Notation dp_mul := (dp_comp do_mul).

  Fixpoint dp_var_list p :=
    match p with
      | dp_nat _      => nil
      | dp_var v      => v::nil
      | dp_par _      => nil
      | dp_comp _ p q => dp_var_list p ++ dp_var_list q
    end.

  Fixpoint dp_par_list p :=
    match p with
      | dp_nat _      => nil
      | dp_var _      => nil
      | dp_par x      => x::nil
      | dp_comp _ p q => dp_par_list p ++ dp_par_list q
    end.

  (* ρ σ ν φ *)

  Fixpoint dp_eval φ ν p := 
    match p with
      | dp_nat n => n
      | dp_var v => φ v
      | dp_par i => ν i
      | dp_comp do_add p q => dp_eval φ ν p + dp_eval φ ν q 
      | dp_comp do_mul p q => dp_eval φ ν p * dp_eval φ ν q 
    end.

  Fact dp_eval_ext φ ν φ' ν' p :
        (forall v, In v (dp_var_list p) -> φ v = φ' v) 
     -> (forall i, In i (dp_par_list p) -> ν i = ν' i) 
     -> dp_eval φ ν p = dp_eval φ' ν' p.
  Proof.
    induction p as [ | | | [] p Hp q Hq ]; simpl; intros H1 H2; f_equal; auto;
      ((apply Hp || apply Hq); intros; [ apply H1 | apply H2 ]; apply in_or_app; auto).
  Qed.

  Fact dp_eval_fix_add φ ν p q : dp_eval φ ν (dp_add p q) = dp_eval φ ν p + dp_eval φ ν q.
  Proof. trivial. Qed.

  Fact dp_eval_fix_mul φ ν p q : dp_eval φ ν (dp_mul p q) = dp_eval φ ν p * dp_eval φ ν q.
  Proof. trivial. Qed.

  Fixpoint dp_size p :=
    match p with
      | dp_nat n => 1
      | dp_var v => 1
      | dp_par i => 1
      | dp_comp _ p q => 1 + dp_size p + dp_size q 
    end.

  Fact dp_size_fix_comp o p q : dp_size (dp_comp o p q) = 1 + dp_size p + dp_size q.
  Proof. auto. Qed.

  Definition dio_single := (dio_polynomial * dio_polynomial)%type.
  Definition dio_single_size (e : dio_single) := dp_size (fst e) + dp_size (snd e).

  Definition dio_single_pred e ν := exists φ, dp_eval φ ν (fst e) = dp_eval φ ν (snd e).

End diophantine_polynomial.

Arguments dp_nat {V P}.
Arguments dp_var {V P}.
Arguments dp_par {V P}.
Arguments dp_comp {V P}.

Notation dp_add := (dp_comp do_add).
Notation dp_mul := (dp_comp do_mul).

Section dio_elem_dio_poly.

  Let dp_2xy u v : dio_polynomial nat nat := dp_mul (dp_nat 2) (dp_mul u v).
  Let dp_x2y2 u v : dio_polynomial nat nat := dp_add (dp_mul u u) (dp_mul v v).

  Let dp_2xy_size u v : dp_size (dp_2xy u v) = 3+dp_size u+dp_size v.
  Proof. auto. Qed.

  Let dp_x2y2_size u v : dp_size (dp_x2y2 u v) = 3+2*dp_size u+2*dp_size v.
  Proof. simpl; omega. Qed.

  Let dp_common e : dio_polynomial nat nat :=
    match e with
      | dee_nat c      => dp_nat c
      | dee_var v      => dp_var v
      | dee_par p      => dp_par p
      | dee_comp o v w => dp_comp o (dp_var v) (dp_var w)
    end.

  Let dp_common_size e : dp_size (dp_common e) <= 3.
  Proof. destruct e as [ | | | [] ]; simpl; auto. Qed.

  Let dp_eval_common φ ν e : dp_eval φ ν (dp_common e) = dee_eval φ ν e.
  Proof. destruct e as [ | | | [] ]; auto. Qed.  

  Let dp_left (c : dio_constraint) := dp_2xy (dp_var (fst c)) (dp_common (snd c)).
  Let dp_right (c : dio_constraint) := dp_x2y2 (dp_var (fst c)) (dp_common (snd c)).
 
  Let dee2dp_1 l := fold_right dp_add (dp_nat 0) (map dp_left l).
  Let dee2dp_2 l := fold_right dp_add (dp_nat 0) (map dp_right l).

  Let dee2dp_1_size l : dp_size (dee2dp_1 l) <= 1+8*length l.
  Proof.
    induction l as [ | (x,e) l IHl ].
    + simpl; auto.
    + unfold dee2dp_1; simpl fold_right; fold (dee2dp_1 l).
      rewrite dp_size_fix_comp.
      unfold dp_left; rewrite dp_2xy_size.
      unfold fst, snd.
      generalize (dp_common_size e); intros.
      simpl dp_size at 1; simpl length.
      rewrite Nat.mul_succ_r; omega.
  Qed.

  Let dee2dp_2_size l : dp_size (dee2dp_2 l) <= 1+12*length l.
  Proof.
    induction l as [ | (x,e) l IHl ].
    + simpl; auto.
    + unfold dee2dp_2; simpl fold_right; fold (dee2dp_2 l).
      rewrite dp_size_fix_comp.
      unfold dp_right; rewrite dp_x2y2_size.
      unfold fst, snd.
      generalize (dp_common_size e); intros.
      simpl dp_size at 1; simpl length.
      rewrite Nat.mul_succ_r; omega.
  Qed.

  Let dc_value_1 φ ν (c : dio_constraint) := 2*(φ (fst c)*dee_eval φ ν (snd c)).
  Let dc_value_2 φ ν (c : dio_constraint) := (φ (fst c)*φ (fst c)) + (dee_eval φ ν (snd c)*dee_eval φ ν (snd c)).

  Let dee2dp_1_eval φ ν l : dp_eval φ ν (dee2dp_1 l) = fold_right plus 0 (map (dc_value_1 φ ν) l).
  Proof.
    induction l as [ | (u,e) l IHl ].
    + simpl; auto.
    + simpl fold_right; rewrite <- IHl.
      unfold dee2dp_1; simpl fold_right.
      rewrite dp_eval_fix_add; f_equal; auto.
      unfold dc_value_1, dp_left, dp_2xy.
      repeat rewrite dp_eval_fix_mul.
      unfold fst, snd; do 2 f_equal.
      apply dp_eval_common.
  Qed.

  Let dee2dp_2_eval φ ν l : dp_eval φ ν (dee2dp_2 l) = fold_right plus 0 (map (dc_value_2 φ ν) l).
  Proof.
    induction l as [ | (u,e) l IHl ].
    + simpl; auto.
    + simpl fold_right; rewrite <- IHl.
      unfold dee2dp_2; simpl fold_right.
      rewrite dp_eval_fix_add; f_equal; auto.
      unfold dc_value_2, dp_right, dp_x2y2.
      rewrite dp_eval_fix_add.
      repeat rewrite dp_eval_fix_mul.
      unfold fst, snd; do 2 f_equal;
      apply dp_eval_common.
  Qed.

  Let dee2dp_spec φ ν l : dp_eval φ ν (dee2dp_1 l) = dp_eval φ ν (dee2dp_2 l)
                      <-> Forall (dc_eval φ ν) l.
  Proof.
    rewrite dee2dp_1_eval, dee2dp_2_eval.
    destruct (list_fun_inv l (0,dee_nat 0)) as (f & Hf).
    rewrite Hf at 1 2.
    do 2 rewrite map_map.
    do 2 rewrite <- sum_fold_map.
    unfold dc_value_1, dc_value_2.
    rewrite convex_n_eq.
    unfold dc_eval.
    apply Forall_forall_map with (P := fun i =>  φ (fst i) = dee_eval φ ν (snd i)); auto.
  Qed.

  Theorem dio_elem_single l : { E : dio_single nat nat | dio_single_size E <= 2+20*length l
              /\ forall ν φ, dp_eval φ ν (fst E) = dp_eval φ ν (snd E) <-> Forall (dc_eval φ ν) l }.
  Proof.
    exists (dee2dp_1 l,dee2dp_2 l); split.
    + unfold dio_single_size, fst, snd.
      generalize (dee2dp_1_size l) (dee2dp_2_size l); intros; omega.
    + unfold dio_single_pred, fst, snd; split; apply dee2dp_spec.
  Defined.

  Theorem dio_elem_equation l : { E : dio_single nat nat | dio_single_size E <= 2+20*length l
                                            /\ forall ν, dio_single_pred E ν <-> exists φ, Forall (dc_eval φ ν) l }.
  Proof.
    destruct (dio_elem_single l) as (p & H1 & H2); exists p; split; auto.
    split; intros (phi & H); exists phi; revert H; apply H2.
  Defined.

End dio_elem_dio_poly.

Corollary dio_rel_single R : 
      𝔻R R -> { E : dio_single nat nat | forall ν, R ν <-> dio_single_pred E ν}.
Proof.
  intros (A & HA).
  destruct dio_formula_elem with (f := A) as (l & _ & _ & Hl).
  destruct dio_elem_equation with (l := l) as (E & _ & HE).
  exists E; intro; rewrite HE, <- Hl, HA; tauto.
Qed.

Section dio_poly_pos.

  Variable P : Set.

  Implicit Type (p : dio_polynomial nat P).

  Definition dio_poly_pos m p : (forall x, In x (dp_var_list p) -> x < m) -> { q | forall φ ν, dp_eval φ ν p = dp_eval (vec_pos (fun2vec 0 m φ)) ν q }.
  Proof.
    induction p as [ n | v | i | o p Hp q Hq ]; intros H.
    + exists (dp_nat n); auto.
    + specialize (H v); spec in H; simpl; auto.
      exists (dp_var (nat2pos H)); intros phi psi; simpl.
      rewrite vec_pos_fun2vec, pos2nat_nat2pos; auto.
    + exists (dp_par i); auto.
    + simpl in H.
      destruct Hp as (p1 & H1). { intros; apply H, in_or_app; auto. }
      destruct Hq as (q1 & H2). { intros; apply H, in_or_app; auto. }
      exists (dp_comp o p1 q1); intros phi psi; simpl.
      destruct o; f_equal; auto.
  Qed.

  Theorem dio_poly_eq_pos (e : dio_single nat P) : { m : nat 
                                                 & { p' : dio_polynomial (pos m) P 
                                                 & { q' | forall ν, dio_single_pred e ν <-> dio_single_pred (p',q') ν } } }.
  Proof.
    destruct e as (p,q).
    destruct (list_upper_bound (dp_var_list p++dp_var_list q)) as (m & Hm).
    destruct (@dio_poly_pos m p) as (p1 & H1). { intros; apply Hm, in_or_app; auto. }
    destruct (@dio_poly_pos m q) as (q1 & H2). { intros; apply Hm, in_or_app; auto. }
    exists m, p1, q1; intros psi; unfold dio_single_pred.
    split; intros (phi & Hphi).
    + exists (vec_pos (fun2vec 0 m phi)); simpl.
      rewrite <- H1, <- H2; auto.
    + exists (vec2fun (vec_set_pos phi) 0).
      rewrite H1, H2.
      rewrite fun2vec_vec2fun.
      eq goal Hphi; f_equal; 
      apply dp_eval_ext; auto; intros j _; rewrite vec_pos_set; auto. 
  Qed.

  Fact dio_poly_eq_pos_equiv n (p q : dio_polynomial (pos n) P) ν : dio_single_pred (p,q) ν <-> exists w, dp_eval (vec_pos w) ν p = dp_eval (vec_pos w) ν q.
  Proof.
    split. 
    + intros (w & Hw); exists (vec_set_pos w); eq goal Hw; f_equal; simpl; apply dp_eval_ext; auto;
        intros; rewrite vec_pos_set; auto.
    + intros (w & Hw); exists (vec_pos w); auto.
  Qed.

End dio_poly_pos.

Check dio_poly_eq_pos.

Section dio_poly_inst_par.

  Variable (V P : Set) (σ : P -> nat).

  Fixpoint dp_inst_par (p : dio_polynomial V P) : dio_polynomial V Empty_set :=
    match p with
      | dp_nat c       => dp_nat c
      | dp_var v       => dp_var v
      | dp_par p       => dp_nat (σ p)
      | dp_comp o p q  => dp_comp o (dp_inst_par p) (dp_inst_par q)
    end.

  Fact dp_inst_par_eval φ ν p : 
    dp_eval φ ν (dp_inst_par p) = dp_eval φ σ p.
  Proof. induction p as [ | | | [] ]; simpl; f_equal; auto. Qed.

End dio_poly_inst_par.

Section dio_poly_ren_par.

  Variable (V P Q : Set) (f : P -> Q).

  Fixpoint dp_ren_par p : dio_polynomial V Q :=
    match p with
      | dp_nat c       => dp_nat c
      | dp_var v       => dp_var v
      | dp_par p       => dp_par (f p)
      | dp_comp o p q  => dp_comp o (dp_ren_par p) (dp_ren_par q)
    end.

  Fact dp_ren_par_eval φ ν p : 
    dp_eval φ ν (dp_ren_par p) = dp_eval φ (fun i => ν (f i)) p.
  Proof. induction p as [ | | | [] ]; simpl; f_equal; auto. Qed.

End dio_poly_ren_par.

Section dio_poly_proj_par.

  Variable (V : Set) (n : nat).

  Fixpoint dp_proj_par p : dio_polynomial V (pos n) :=
    match p with
      | dp_nat c       => dp_nat c
      | dp_var v       => dp_var v
      | dp_par p       => match le_lt_dec n p with left _ => dp_nat 0 | right H => dp_par (nat2pos H) end
      | dp_comp o p q  => dp_comp o (dp_proj_par p) (dp_proj_par q)
    end.

  Fact dp_proj_par_eval φ ν p : 
    dp_eval φ ν (dp_proj_par p) = dp_eval φ (fun i => match le_lt_dec n i with left _ => 0 | right H => ν (nat2pos H) end) p.
  Proof. 
    induction p as [ | | p | [] ]; simpl; f_equal; auto.
    destruct (le_lt_dec n p); auto.
  Qed.
      
End dio_poly_proj_par.


