(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Elementary diophantine constraints *)

Require Import List Arith Nat Omega.
Require Import utils_list gcd prime dio_logic.

Set Implicit Arguments.

Section interval.

  (** A small interval & valuation library *)

  Definition interval := (nat * nat)%type. (* (a,b) <~~~> [a,b[ *)

  Implicit Types (i j : interval).

  Definition in_interval i x := let (a,b) := i in a <= x < b.
  Definition out_interval i x := let (a,b) := i in x < a \/ b <= x.
  Definition interval_disjoint i j := forall x, in_interval i x -> in_interval j x -> False.

  Definition interval_union (i j : interval) :=
    match i, j with (a1,b1),(a2,b2) => (min a1 a2, max b1 b2) end.

  Fact in_out_interval i x : in_interval i x -> out_interval i x -> False.
  Proof. destruct i; simpl; omega. Qed.

  Fact in_out_interval_dec i x : { in_interval i x } + { out_interval i x }.
  Proof. 
    destruct i as (a,b); simpl.
    destruct (le_lt_dec a x); destruct (le_lt_dec b x); try (left; omega);right; omega.
  Qed. 

  Fact interval_union_left i j x : in_interval i x -> in_interval (interval_union i j) x.
  Proof.
    revert i j; intros (a,b) (u,v); simpl.
    generalize (Nat.le_min_l a u) (Nat.le_max_l b v); omega.
  Qed.

  Fact interval_union_right i j x : in_interval j x -> in_interval (interval_union i j) x.
  Proof.
    revert i j; intros (a,b) (u,v); simpl.
    generalize (Nat.le_min_r a u) (Nat.le_max_r b v); omega.
  Qed.

  Definition valuation_union i1 (g1 : nat -> nat) i2 g2 : 
               interval_disjoint i1 i2 
            -> { g | (forall x, in_interval i1 x -> g x = g1 x)
                  /\ (forall x, in_interval i2 x -> g x = g2 x) }.
  Proof.
    intros H2.
    exists (fun x => if in_out_interval_dec i1 x then g1 x else g2 x).
    split; intros x Hx.
    + destruct (in_out_interval_dec i1 x) as [ | H3 ]; auto.
      exfalso; revert Hx H3; apply in_out_interval.
    + destruct (in_out_interval_dec i1 x) as [ H3 | ]; auto.
      exfalso; revert H3 Hx; apply H2.
  Qed.

  Definition valuation_one_union k v i1 (g1 : nat -> nat) i2 g2 : 
               ~ in_interval (interval_union i1 i2) k 
            -> interval_disjoint i1 i2 
            -> { g | g k = v /\ (forall x, in_interval i1 x -> g x = g1 x)
                             /\ (forall x, in_interval i2 x -> g x = g2 x) }.
  Proof.
    intros H1 H2.
    exists (fun x => if eq_nat_dec x k then v 
                     else if in_out_interval_dec i1 x then g1 x 
                     else g2 x).
    split; [ | split ].
    + destruct (eq_nat_dec k k) as [ | [] ]; auto.
    + intros x Hx.
      destruct (eq_nat_dec x k) as [ | ].
      * subst; destruct H1; apply interval_union_left; auto.
      * destruct (in_out_interval_dec i1 x) as [ | H3 ]; auto.
        exfalso; revert Hx H3; apply in_out_interval.
    + intros x Hx.
      destruct (eq_nat_dec x k) as [ | ].
      * subst; destruct H1; apply interval_union_right; auto.
      * destruct (in_out_interval_dec i1 x) as [ H3 | ]; auto.
        exfalso; revert H3 Hx; apply H2.
  Qed.

End interval.

Section diophantine_system.

  (* v : cst = nat      constant (natural number)
     p q : par = nat    parameter 
     x y z : var = nat  existentially quantified variable 
   
     equations are of 4 types 
       1) x = v 
       2) x = p 
       3) x = y + z 
       4) x = y * z 

     We represent a relation between parameters R by a list of equations l and one
     variable x : var such that
       a) for any value f : nat -> nat of the params, l[f] has a solution
       b) for any value f : nat -> nat of the params,

                R f <-> ((x=0)::l)[f] has a solution

     How do we simulate poly1 = poly2 linearly ?

         poly1 = (eqn1,x) where x is output
         poly2 = (eqn2,y) where y is output

         example poly1 = p*(q+r)
         gives eqn1:= (0=1*2, 1=p, 2=3+4, 3=q, 4=r) and x:=0

         then we simulate poly1 = poly2 with
 
               poly1 = poly2 <-> (eqn1 U eqn2 U { w=y+u, w=x+v, z=u+v }, z)

         where u v z w are fresh

     We implement conjunction (cap), disjunction (cup) and exists so that we get a linear encoding

      cap) R by (lR,xR) and S by (lS,xS) 
           we assume (lR,xR) and (lS,xS) do not share existential variables
           (always possible by renaming those of S)

           R cap S = (lR U lS U { z = x+y },z) where z is fresh
 
      cup) R cup S = (lR U lS U { z = x*y },z)

      exists) ∃n.R f{p<-n} = (lR[p<-0], ...)

   *)

  Inductive dio_elem_expr : Set :=
    | dee_nat  : nat -> dio_elem_expr   (* c : constant *)
    | dee_var  : nat -> dio_elem_expr   (* v : existentially quant. var *)
    | dee_par  : nat -> dio_elem_expr   (* p : parameter *)
    | dee_comp : dio_op -> nat -> nat -> dio_elem_expr. (* v1 op v2 *)

  Notation dee_add := (dee_comp do_add).
  Notation dee_mul := (dee_comp do_mul).

  (* ρ σ ν φ *)

  Definition dee_eval φ ν e := 
    match e with
      | dee_nat n => n
      | dee_var v => φ v
      | dee_par i => ν i
      | dee_comp o v w => do_eval o (φ v) (φ w) 
    end.

  Definition dee_vars e x  :=
    match e with
      | dee_nat _ => False
      | dee_var v => x = v
      | dee_par _ => False
      | dee_comp _ v w => x = v \/ x = w
    end.

  Fact dee_eval_ext e φ1 ν1 φ2 ν2  : 
        (forall x, dee_vars e x -> φ1 x = φ2 x) 
     -> (forall x, ν1 x = ν2 x)
     -> dee_eval φ1 ν1 e = dee_eval φ2 ν2 e.
  Proof. destruct e as [ | | | [] ]; simpl; auto. Qed.

  (* ρ σ ν *)

  Definition dee_move k p :=
    match p with
      | dee_nat n      => dee_nat n
      | dee_var v      => dee_var (k+v)
      | dee_par i      => dee_par i
      | dee_comp o v w => dee_comp o (k+v) (k+w)
    end.

  Fact dee_eval_move k φ ν e : dee_eval φ ν (dee_move k e) = dee_eval (fun x => φ (k+x)) ν e.
  Proof. destruct e as [ | | | [] ]; simpl; auto. Qed.

  Fact dee_vars_move k e x : dee_vars (dee_move k e) x <-> exists y, dee_vars e y /\ x = k+y.
  Proof. destruct e as [ | | | [] ]; simpl; firstorder. Qed.

  Definition dee_dec k e :=
    match e with
      | dee_nat n      => dee_nat n
      | dee_var v      => dee_var v
      | dee_par 0      => dee_var k 
      | dee_par (S i)  => dee_par i
      | dee_comp o v w => dee_comp o v w
    end.

  Fact dee_eval_dec φ ν k e : dee_eval φ ν (dee_dec k e) = dee_eval φ (fun x => match x with 0 => φ k | S x => ν x end) e.
  Proof. destruct e as [ | | [] | [] ]; simpl; auto. Qed.

  Fact dee_vars_dec k e x : dee_vars (dee_dec k e) x -> x = k \/ dee_vars e x.
  Proof. destruct e as [ | | [] | [] ]; simpl; firstorder. Qed.

  Definition dio_constraint := (nat * dio_elem_expr)%type.

  Implicit Type (c : dio_constraint).

  Definition dc_eval φ ν c := φ (fst c) = dee_eval φ ν (snd c).

  Arguments dc_eval φ ν c /.
  
  Definition dc_vars c x := x = fst c \/ dee_vars (snd c) x.

  Arguments dc_vars c x /.

  Fact dc_eval_ext c φ1 ν1 φ2 ν2  : 
        (forall x, dc_vars c x -> φ1 x = φ2 x) 
     -> (forall x, ν1 x = ν2 x)
     -> dc_eval φ1 ν1 c <-> dc_eval φ2 ν2 c.
  Proof.
    intros H1 H2.
    destruct c as (v,e); unfold dc_eval; simpl.
    rewrite H1; simpl; auto.
    rewrite dee_eval_ext with e φ1 ν1 φ2 ν2; try tauto.
    intros; apply H1; simpl; auto.
  Qed.

  Definition dc_move k c := (k+fst c, dee_move k (snd c)).

  Fact dc_eval_move k φ ν c : dc_eval φ ν (dc_move k c) <-> dc_eval (fun x => φ (k+x)) ν c.
  Proof.
    destruct c as (v,e); simpl.
    rewrite dee_eval_move; tauto.
  Qed.

  Fact dc_vars_move k c x : dc_vars (dc_move k c) x <-> exists y, x = k + y /\ dc_vars c y.
  Proof.
    destruct c as (v,e); simpl.
    rewrite dee_vars_move.
    split.
    + intros [ ? | (y & Hy & ?) ]; subst x; firstorder; exists v; auto.
    + intros (y & ? & [ | ]); subst; firstorder.
  Qed.

  Definition dc_dec k c := (fst c, dee_dec k (snd c)).

  Fact dc_eval_dec φ ν k c : dc_eval φ ν (dc_dec k c) <-> dc_eval φ  (fun x => match x with 0 => φ k | S x => ν x end) c.
  Proof. destruct c; simpl; rewrite dee_eval_dec; tauto. Qed.

  Fact dc_vars_dec k c x : dc_vars (dc_dec k c) x -> x = k \/ dc_vars c x.
  Proof. destruct c; simpl; intros [ | H ]; auto; apply dee_vars_dec in H; tauto. Qed.

  Implicit Type (R : (nat -> nat) -> Prop).

  (* A diophantine system for R is an interval i, a list l of constraints, a reference variable x
     such that
       1) the variables in l U {x} and belong to i
       2) for any valuation, the equations of l are satisfiable
       3) for any valuation ν, R ν holds iff the equations of { x=0 } U l are satisfiable
   *)

  Record dio_repr_at R a n l := {
    ds_eqns : list dio_constraint;
    ds_ref  : nat;
    ds_H0   : length ds_eqns = l;
    ds_H1   : forall x c, In c ds_eqns -> dc_vars c x -> a <= x < a+n;
    ds_H2   : a <= ds_ref < a+n;
    ds_H3   : forall ν, exists φ, Forall (dc_eval φ ν) ds_eqns;
    ds_H4   : forall ν, R ν <-> exists φ, Forall (dc_eval φ ν) ds_eqns /\ φ ds_ref = 0;
  }.

  Section diophantine_sys_expr.

    (* A compiler from expressions to lists of small expressions *)

    Fixpoint de_eqns e x :=
      match e with
        | de_cst n      => (x,dee_nat n)::nil 
        | de_var p      => (x,dee_par p)::nil
        | de_comp o p q => (x,dee_comp o (x+1) (x+1+de_size p)) :: de_eqns p (x+1) ++ de_eqns q (x+1+de_size p)
      end.

    Fact de_eqns_length e x : length (de_eqns e x) = de_size e.
    Proof.
      revert x; induction e as [ | | o p Hp q Hq ]; intros x; simpl; auto.
      rewrite app_length, Hp, Hq; auto.
    Qed.

    Fact de_size_ge_1 e : 1 <= de_size e.
    Proof. destruct e; simpl; omega. Qed.

    Fact de_eqns_vars e x : forall c, In c (de_eqns e x) -> forall y, dc_vars c y -> x <= y < x+de_size e.
    Proof.
      revert x; induction e as [ | | o p Hp q Hq ]; intros x; simpl; auto.
      + intros ? [ [] | [] ]; simpl; intros; omega.
      + intros ? [ [] | [] ]; simpl; intros; omega.
      + intros c [ Hc | Hc ]; [ | apply in_app_or in Hc; destruct Hc as [ Hc | Hc ] ]; subst; simpl.
        * intros; generalize (de_size_ge_1 q); intros; omega.
        * intros y Hy; apply Hp with (y := y) in Hc; simpl in *; auto; omega.
        * intros y Hy; apply Hq with (y := y) in Hc; simpl in *; auto; omega.
    Qed.

    (* If equations in de_eqns e x are satisfied in φ, then φ x must be equal to de_eval ν e *)

    Fact dc_Forall_eval φ ν e x : Forall (dc_eval φ ν) (de_eqns e x) -> de_eval ν e = φ x.
    Proof.
      rewrite Forall_forall.
      revert x; induction e as [ | v| [] p Hp q Hq ]; simpl; intros x Hx; simpl; auto.
      * specialize (Hx (x,dee_nat n)); simpl in Hx; rewrite Hx; auto.
      * specialize (Hx (x,dee_par v)); simpl in Hx; rewrite Hx; auto.
      * rewrite Hp with (x+1), Hq with (x+1+de_size p).
        - symmetry; apply (Hx (_, dee_add _ _)); auto.
        - intros; apply Hx; right; apply in_or_app; auto.
        - intros; apply Hx; right; apply in_or_app; auto.
      * rewrite Hp with (x+1), Hq with (x+1+de_size p).
        - symmetry; apply (Hx (_, dee_mul _ _)); auto.
        - intros; apply Hx; right; apply in_or_app; auto.
        - intros; apply Hx; right; apply in_or_app; auto.
    Qed.

    (* Converselly, equations in de_eqns e x are satisfiable *)

    Fact dc_eval_exists_Forall ν e x : { φ | Forall (dc_eval φ ν) (de_eqns e x) }. 
    Proof.
      revert x; induction e as [ | v | o p Hp q Hq ]; simpl; intros x.
      + exists (fun  _ => n); constructor; simpl; auto.
      + exists (fun  _ => ν v); constructor; simpl; auto.
      + destruct (Hp (x+1)) as (g1 & H2).
        destruct (Hq (x+1+de_size p)) as (g2 & H4).
        generalize (dc_Forall_eval _ _ H2) (dc_Forall_eval _ _ H4); intros H1 H3.
        destruct (@valuation_one_union x (do_eval o (de_eval ν p) (de_eval ν q)) (x+1,x+1+de_size p) g1 (x+1+de_size p, x+1+de_size p+de_size q) g2)
           as (g & H5 & H6 & H7).
        * simpl; rewrite Min.min_l; omega.
        * intros y; simpl; omega.
        * exists g; constructor.
          - red; unfold fst, snd; rewrite H5, H1, H3; simpl; f_equal; symmetry.
            ++ apply H6; simpl; generalize (de_size_ge_1 p); intros; omega.
            ++ apply H7; simpl; generalize (de_size_ge_1 q); intros; omega.
          - apply Forall_app; split.
            ++ revert H2; do 2 rewrite Forall_forall.
               intros H c Hc.
               generalize (H _ Hc); apply dc_eval_ext; auto.
               intros y Hy; apply H6.
               apply de_eqns_vars with (1 := Hc); auto.
            ++ revert H4; do 2 rewrite Forall_forall.
               intros H c Hc.
               generalize (H _ Hc); apply dc_eval_ext; auto.
               intros y Hy; apply H7.
               apply de_eqns_vars with (1 := Hc); auto.
    Qed.

    Let compare_lemma x y : { u : nat & { v | u+x = v+y } }.
    Proof.
      destruct (le_lt_dec x y).
      + exists (y-x), 0; omega.
      + exists 0, (x-y); omega.
    Qed.

    (* poly1 = poly2 <-> (eqn1 U eqn2 U { w=x+u, w=y+v, z=u+v }, z) *)

    Let g0 (n x0 x1 x2 x3 m : nat) := if le_lt_dec n m then 
                                match m - n with
                                  | 0 => x0
                                  | 1 => x1
                                  | 2 => x2
                                  | _ => x3
                                end
                              else x3.

    Let g0_0 (n x0 x1 x2 x3 : nat) : g0 n x0 x1 x2 x3 n = x0.
    Proof. 
      unfold g0; destruct (le_lt_dec n n); try omega.
      replace (n-n) with 0 by omega; auto.
    Qed.

    Let g0_1 (n x0 x1 x2 x3 : nat) : g0 n x0 x1 x2 x3 (n+1) = x1.
    Proof. 
      unfold g0; destruct (le_lt_dec n (n+1)); try omega.
      replace (n+1-n) with 1 by omega; auto.
    Qed.

    Let g0_2 (n x0 x1 x2 x3 : nat) : g0 n x0 x1 x2 x3 (n+2) = x2.
    Proof. 
      unfold g0; destruct (le_lt_dec n (n+2)); try omega.
      replace (n+2-n) with 2 by omega; auto.
    Qed.

    Let g0_3 (n x0 x1 x2 x3 : nat) : g0 n x0 x1 x2 x3 (n+3) = x3.
    Proof. 
      unfold g0; destruct (le_lt_dec n (n+3)); try omega.
      replace (n+3-n) with 3 by omega; auto.
    Qed.

    (* x1+(x2*5) at 4 ~~> v4 = v5 + v6, v5 = x1, v6 = v7 * v8, v7 = x2, v8 = 5
       x3 at 9        ~~> v9 = x3

       x1+(x2*5) = x3 at 0
                      ~~> v3 = v1 + v4, v3 = v2 + v9, v0 = v1 + v2
    *)

    Lemma dio_repr_at_eq n e1 e2 : dio_repr_at (fun ν => de_eval ν e1 = de_eval ν e2) n (4+de_size e1+de_size e2) (3+de_size e1+de_size e2).
    Proof.
      exists ((n+3, dee_add (n+1) (n+4)) ::
              (n+3, dee_add (n+2) (n+4+de_size e1)) ::
              (n,   dee_add (n+1) (n+2)) ::
              (de_eqns e1 (n+4) ++ de_eqns e2 (n+4+de_size e1))) n.
      + simpl; rewrite app_length; do 2 rewrite de_eqns_length; auto.
      + intros x c [ Hc | [ Hc | [ Hc | Hc ] ] ].
        * subst; simpl; generalize (de_size_ge_1 e2); omega.
        * subst; simpl; generalize (de_size_ge_1 e2); omega.
        * subst; simpl; generalize (de_size_ge_1 e2); omega.
        * intros Hx; apply in_app_or in Hc.
          destruct Hc as [ Hc | Hc ]; apply de_eqns_vars with (2 := Hx) in Hc;
             simpl in *; omega.
      + simpl; omega.
      + intros f.
        destruct (@dc_eval_exists_Forall f e1 (n+4)) as (g1 & H2).
        destruct (@dc_eval_exists_Forall f e2 (n+4+de_size e1)) as (g2 & H4).
        destruct (compare_lemma (g1 (n+4)) (g2 (n+4+de_size e1))) as (u & v & Huv).
        set (g3 := g0 n (u+v) u v (u+g1 (n+4))).
        destruct (@valuation_union (n+4, n+4+de_size e1) g1 (n+4+de_size e1, n+4+de_size e1+de_size e2) g2)
           as (g4 & H5 & H6).
        { intro; simpl; omega. }
        destruct (@valuation_union (n,n+4) g3 (n+4,n+4+de_size e1+de_size e2) g4) 
           as (g & H7 & H8).
        { intro; simpl; omega. }
        generalize (de_size_ge_1 e1) (de_size_ge_1 e2); intros E1 E2.
        exists g; repeat constructor; simpl.
        * rewrite H7, H7; simpl; auto; try omega.
          rewrite H8; simpl; try omega.
          rewrite H5; simpl; try omega.
          unfold g3; rewrite g0_1, g0_3; omega.
        * rewrite H7, H7; simpl; auto; try omega.
          rewrite H8; simpl; try omega.
          rewrite H6; simpl; auto; try omega.
          unfold g3; rewrite g0_2, g0_3; omega.
        * rewrite H7, H7, H7; simpl; try omega.
          unfold g3; rewrite g0_0, g0_1, g0_2; auto.
        * apply Forall_app; split.
          - revert H2; do 2 rewrite Forall_forall.
            intros H c Hc; generalize (H _ Hc).
            apply dc_eval_ext; auto.
            intros x Hx; rewrite H8.
            ++ apply H5, de_eqns_vars with (1 := Hc); auto.
            ++ apply de_eqns_vars with (1 := Hc) in Hx.
               simpl in *; omega.
          - revert H4; do 2 rewrite Forall_forall.
            intros H c Hc; generalize (H _ Hc).
            apply dc_eval_ext; auto.
            intros x Hx; rewrite H8.
            ++ apply H6, de_eqns_vars with (1 := Hc); auto.
            ++ apply de_eqns_vars with (1 := Hc) in Hx.
               simpl in *; omega.
      + intros f; split.
        * intros Hf.
          destruct (@dc_eval_exists_Forall f e1 (n+4)) as (g1 & H2).
          destruct (@dc_eval_exists_Forall f e2 (n+4+de_size e1)) as (g2 & H4).
          generalize (dc_Forall_eval _ _ H2) (dc_Forall_eval _ _ H4); intros H1 H3.
          set (g3 := g0 n 0 0 0 (de_eval f e1)).
          destruct (@valuation_union (n+4, n+4+de_size e1) g1 (n+4+de_size e1, n+4+de_size e1+de_size e2) g2)
             as (g4 & H5 & H6).
          { intro; simpl; omega. }
          destruct (@valuation_union (n, n+4) g3 (n+4, n+4+de_size e1+de_size e2) g4) 
            as (g & H7 & H8).
          { intro; simpl; omega. }
          generalize (de_size_ge_1 e1) (de_size_ge_1 e2); intros E1 E2.
          exists g; repeat constructor; simpl.
          - rewrite H7, H7; simpl; auto; try omega.
            rewrite H8; simpl; try omega.
            rewrite H5; simpl; try omega.
            unfold g3; rewrite g0_3, g0_1; omega.
          - rewrite H7, H7; simpl; auto; try omega.
            rewrite H8; simpl; try omega.
            unfold g3; rewrite g0_3, g0_2.
            rewrite Hf, H6; simpl; auto; omega.
          - rewrite H7, H7, H7; simpl; try omega.
            unfold g3; rewrite g0_0, g0_1, g0_2; auto.
          - apply Forall_app; split.
            ++ revert H2; do 2 rewrite Forall_forall.
               intros H c Hc; generalize (H _ Hc).
               apply dc_eval_ext; auto.
               intros x Hx; rewrite H8.
               ** apply H5, de_eqns_vars with (1 := Hc); auto.
               ** apply de_eqns_vars with (1 := Hc) in Hx.
                  simpl in *; omega.
            ++ revert H4; do 2 rewrite Forall_forall.
               intros H c Hc; generalize (H _ Hc).
               apply dc_eval_ext; auto.
               intros x Hx; rewrite H8.
               ** apply H6, de_eqns_vars with (1 := Hc); auto.
               ** apply de_eqns_vars with (1 := Hc) in Hx.
                  simpl in *; omega.
          - rewrite H7; simpl; try omega.
            unfold g3; rewrite g0_0; auto.
        * intros (g & H1 & H0).
          do 3 rewrite Forall_cons_inv in H1.
          rewrite Forall_app in H1.
          destruct H1 as (H1 & H2 & H3 & H4 & H5).
          simpl in *.
          rewrite dc_Forall_eval with (1 := H4).
          rewrite dc_Forall_eval with (1 := H5).
          omega.
    Defined.

  End diophantine_sys_expr.

  Let not_interval_union a1 n1 a2 n2 : 
           a1+n1 <= a2
        -> ~ in_interval (interval_union (a1, a1 + n1) (a2, a2 + n2)) (a2 + n2).
  Proof.
    simpl; intros H1 (_ & H3).
    rewrite Nat.max_r in H3; omega.
  Qed.

  Lemma dio_repr_at_conj R1 a1 n1 p1 R2 a2 n2 p2 n : 
          dio_repr_at R1 a1 n1 p1
       -> dio_repr_at R2 a2 n2 p2
       -> a1+n1 <= a2
       -> n = 1+a2+n2-a1
       -> dio_repr_at (fun ν => R1 ν /\ R2 ν) a1 n (1+p1+p2).
  Proof.
    intros [ l1 r1 F0 F1 F2 F3 F4 ] [ l2 r2 G0 G1 G2 G3 G4 ] H12 ?; subst n.
    exists ((a2+n2,dee_add r1 r2)::l1++l2) (a2+n2).
    + simpl; rewrite app_length, F0, G0; omega.
    + replace (a1+(1+a2+n2-a1)) with (1+a2+n2) by omega.
      intros x c [ Hc | Hc ].
      * subst; simpl; omega.
      * intros H1; apply in_app_or in Hc; destruct Hc as [ Hc | Hc ].
        - specialize (F1 _ _ Hc H1); omega.
        - specialize (G1 _ _ Hc H1); omega.
    + omega.
    + intros f.
      destruct (F3 f) as (g1 & H1).
      destruct (G3 f) as (g2 & H2).
      destruct (@valuation_one_union (a2+n2) (g1 r1+g2 r2) (a1,a1+n1) g1 (a2,a2+n2) g2) 
        as (g & Hg1 & Hg2 & Hg3); auto.
      { red; simpl; intros; omega. }
      exists g; constructor; [ | apply Forall_app; split ].
      * simpl; rewrite (Hg2 r1), (Hg3 r2); auto.
      * apply Forall_impl with (2 := H1).
        intros c Hc; apply dc_eval_ext; auto.
        intros x Hx; apply Hg2, F1 with c; auto.
      * apply Forall_impl with (2 := H2).
        intros c Hc; apply dc_eval_ext; auto.
        intros x Hx; apply Hg3, G1 with c; auto.
    + intros f; rewrite F4, G4; split.
      * intros ((g1 & H1 & H2) & (g2 & H3 & H4)).
        destruct (@valuation_one_union (a2+n2) 0 (a1,a1+n1) g1 (a2,a2+n2) g2) 
          as (g & Hg1 & Hg2 & Hg3); auto.
        { red; simpl; intros; omega. }
        exists g; split; auto; constructor; simpl.
        ++ rewrite Hg1, Hg2, Hg3; auto; omega.
        ++ apply Forall_app; split.
           ** apply Forall_impl with (2 := H1).
              intros c Hc; apply dc_eval_ext; auto.
              intros x Hx; apply Hg2, F1 with c; auto.
           ** apply Forall_impl with (2 := H3).
              intros c Hc; apply dc_eval_ext; auto.
              intros x Hx; apply Hg3, G1 with c; auto.
      * intros (g & Hg1 & Hg2).
        inversion Hg1 as [ | ? ? Hg3 Hg4 ].
        apply Forall_app in Hg4; destruct Hg4 as (Hg4 & Hg5).
        simpl in Hg3; split; exists g; split; auto; omega.
  Defined.

  Lemma dio_repr_at_disj R1 a1 n1 p1 R2 a2 n2 p2 n : 
          dio_repr_at R1 a1 n1 p1
       -> dio_repr_at R2 a2 n2 p2
       -> a1+n1 <= a2
       -> n = 1+a2+n2-a1
       -> dio_repr_at (fun ν => R1 ν \/ R2 ν) a1 n (1+p1+p2). 
  Proof.
    intros [ l1 r1 F0 F1 F2 F3 F4 ] [ l2 r2 G0 G1 G2 G3 G4 ] H12 ?; subst n.
    exists ((a2+n2,dee_mul r1 r2)::l1++l2) (a2+n2).
    + simpl; rewrite app_length, F0, G0; omega.
    + replace (a1+(1+a2+n2-a1)) with (1+a2+n2) by omega.
      intros x c [ Hc | Hc ].
      * subst; simpl; omega.
      * intros H1; apply in_app_or in Hc; destruct Hc as [ Hc | Hc ].
        - specialize (F1 _ _ Hc H1); omega.
        - specialize (G1 _ _ Hc H1); omega.
    + omega.
    + intros f.
      destruct (F3 f) as (g1 & H1).
      destruct (G3 f) as (g2 & H2).
      destruct (@valuation_one_union (a2+n2) (g1 r1*g2 r2) (a1,a1+n1) g1 (a2,a2+n2) g2) 
        as (g & Hg1 & Hg2 & Hg3); auto.
      { red; simpl; intros; omega. }
      exists g; constructor; [ | apply Forall_app; split ].
      * simpl; rewrite (Hg2 r1), (Hg3 r2); auto.
      * apply Forall_impl with (2 := H1).
        intros c Hc; apply dc_eval_ext; auto.
        intros x Hx; apply Hg2, F1 with c; auto.
      * apply Forall_impl with (2 := H2).
        intros c Hc; apply dc_eval_ext; auto.
        intros x Hx; apply Hg3, G1 with c; auto.
    + intros f; rewrite F4, G4; split.
      * intros [ (g1 & H1 & H2) | (g2 & H1 & H2) ].
        - destruct (G3 f) as (g2 & H3).
          destruct (@valuation_one_union (a2+n2) 0 (a1,a1+n1) g1 (a2,a2+n2) g2) 
            as (g & Hg1 & Hg2 & Hg3); auto.
          { red; simpl; intros; omega. }
          exists g; split; auto.
          constructor; simpl; [ | apply Forall_app; split ].
          ++ rewrite Hg1, Hg2, H2; auto.
          ++ apply Forall_impl with (2 := H1).
             intros c Hc; apply dc_eval_ext; auto.
             intros x Hx; apply Hg2, F1 with c; auto.
          ++ apply Forall_impl with (2 := H3).
             intros c Hc; apply dc_eval_ext; auto.
             intros x Hx; apply Hg3, G1 with c; auto.
        - destruct (F3 f) as (g1 & H3).
          destruct (@valuation_one_union (a2+n2) 0 (a1,a1+n1) g1 (a2,a2+n2) g2) 
            as (g & Hg1 & Hg2 & Hg3); auto.
          { red; simpl; intros; omega. }
          exists g; split; auto.
          constructor; simpl; [ | apply Forall_app; split ].
          ++ rewrite Hg1, (Hg3 r2), H2, mult_comm; auto.
          ++ apply Forall_impl with (2 := H3).
             intros c Hc; apply dc_eval_ext; auto.
             intros x Hx; apply Hg2, F1 with c; auto.
          ++ apply Forall_impl with (2 := H1).
             intros c Hc; apply dc_eval_ext; auto.
             intros x Hx; apply Hg3, G1 with c; auto.
      * intros (g & Hg1 & Hg2).
        inversion Hg1 as [ | ? ? Hg3 Hg4 ].
        apply Forall_app in Hg4; destruct Hg4 as (Hg4 & Hg5).
        simpl in Hg3; rewrite Hg2 in Hg3.
        symmetry in Hg3; apply mult_is_O in Hg3.
        destruct Hg3 as [ Hg3 | Hg3 ]; [ left | right ]; exists g; auto.
  Defined.

  Lemma dio_repr_at_exst R a n m p : 
          dio_repr_at R a n p
       -> m = n+1
       -> dio_repr_at (fun ν => exists n, R (dv_lift ν n)) a m p. 
  Proof.
    intros [ l r F0 F1 F2 F3 F4 ] ?; subst m.
    exists (map (dc_dec (a+n)) l) r.
    + rewrite map_length; auto.
    + intros x c'; rewrite in_map_iff.
      intros (c & E & Hc) H; subst.
      apply dc_vars_dec in H.
      destruct H as [ | H ]; subst; simpl; try omega.
      apply F1 in H; simpl in *; auto; omega.
    + omega.
    + intros f.
      destruct (F3 (fun x => match x with 0 => 0 | S x => f x end)) as (g & Hg).
      exists (fun x => if eq_nat_dec x (a+n) then 0 else g x).
      rewrite Forall_map.
      apply Forall_impl with (2 := Hg). 
      intros c Hc; rewrite dc_eval_dec; apply dc_eval_ext; auto.
      * intros x Hx.
        destruct (eq_nat_dec x (a+n)); subst; auto.
        apply F1 in Hx; auto; omega.
      * intros [ | x ]; auto.
        destruct (eq_nat_dec (a+n) (a+n)); tauto.
    + intros f; split.
      * intros (u & Hu).
        apply F4 in Hu.
        destruct Hu as (g & H1 & H2).
        exists (fun x => if eq_nat_dec x (a+n) then u else g x); simpl; split.
        - rewrite Forall_map.
          apply Forall_impl with (2 := H1).
          intros c Hc; rewrite dc_eval_dec; apply dc_eval_ext; auto.
          ++ intros x Hx.
             destruct (eq_nat_dec x (a+n)); auto.
             subst x; apply F1 in Hx; auto; omega.
          ++ intros [ | x ]; auto.
             destruct (eq_nat_dec (a+n) (a+n)); tauto.
        - destruct (eq_nat_dec r (a+n)); auto.
          subst; omega.
      * intros (g & H1 & H2).
        exists (g (a+n)); rewrite F4.
        exists g; split; auto.
        revert H1; do 2 rewrite Forall_forall.
        intros H c Hc.
        apply in_map with (f := dc_dec _), H in Hc.
        revert Hc; rewrite dc_eval_dec; apply dc_eval_ext; auto.
  Defined.

  Fixpoint df_weight_1 f :=
    match f with
      | df_atm a b  => 4 + de_size a + de_size b
      | df_conj f g => 1 + df_weight_1 f + df_weight_1 g  
      | df_disj f g => 1 + df_weight_1 f + df_weight_1 g  
      | df_exst f   => 1 + df_weight_1 f
    end.

  Fact df_weigth_1_size f : df_weight_1 f <= 4*df_size f.
  Proof. induction f; simpl; omega. Qed.

  Fixpoint df_weight_2 f :=
    match f with
      | df_atm a b  => 3 + de_size a + de_size b
      | df_conj f g => 1 + df_weight_2 f + df_weight_2 g  
      | df_disj f g => 1 + df_weight_2 f + df_weight_2 g  
      | df_exst f   => df_weight_2 f
    end.

  Fact df_weigth_2_size f : df_weight_2 f <= 3*df_size f.
  Proof. induction f; simpl in *; omega. Qed.

  Lemma dio_repr_at_form n f : dio_repr_at (df_pred f) n (df_weight_1 f) (df_weight_2 f).
  Proof.
    revert n;
    induction f as [ a b | f IHf g IHg | f IHf g IHg | f IHf ]; intros n; simpl df_pred; simpl df_weight_1; simpl df_weight_2.
    + apply dio_repr_at_eq.
    + apply dio_repr_at_conj with (n1 := df_weight_1 f) (a2 := n+df_weight_1 f) (n2 := df_weight_1 g); auto; omega.
    + apply dio_repr_at_disj with (n1 := df_weight_1 f) (a2 := n+df_weight_1 f) (n2 := df_weight_1 g); auto; omega.
    + apply dio_repr_at_exst with (n := df_weight_1 f); auto; omega.
  Defined.

  (** For any diophantine logic formula f of size s, one can compute a list l 
      of at most 1+3*s elementary diophantine constraints, containing at 
      most 4*s variables and such that df_pred f ν is equivalent to 
      the simultaneous satisfiability at ν of all the elementary constraints in l *)

  Theorem dio_formula_elem f : { l | length l <= 1+3*df_size f
                                 /\ (forall c x, In c l -> dc_vars c x -> x < 4*df_size f)  
                                 /\  forall ν, df_pred f ν <-> exists φ, Forall (dc_eval φ ν) l }.
  Proof.
    destruct (dio_repr_at_form 0 f) as [l r H0 H1 H2 H3 H4].
    exists ((r,dee_nat 0) :: l); split; [ | split ]; simpl length; try omega.
    + rewrite H0; apply le_n_S, df_weigth_2_size.
    + intros c x [ [] | H ].
      * simpl dc_vars; intros [ | [] ]; subst.
        generalize (df_weigth_1_size f); intros; omega.
      * intros G; apply H1 in G; auto.
        generalize (df_weigth_1_size f); intros; omega.
    + intros ν; rewrite H4.
      split; intros (φ & H); exists φ; revert H; rewrite Forall_cons_inv; simpl; tauto.
  Defined.

  Definition dio_fs f := proj1_sig (dio_formula_elem f).
                 
End diophantine_system.

(* Check dio_formula_elem.
Print Assumptions dio_formula_elem. *)
