(** * The very classical example of GCD computation in Hoare logic.

 This file is part of the "Tutorial on Hoare Logic". 
 For an introduction to this Coq library, 
 see README #or <a href=index.html>index.html</a>#.

 This file illustrates how to use the Hoare logic described in file
 #<a href="hoarelogicsemantics.html">#[hoarelogicsemantics]#</a>#


 I use here the very classical example of "great common divisor"
 computations through successive subtractions.
*)

Set Implicit Arguments.

Require Import ZArith.
Require Import Znumtheory.
Require Import Bool.
Require Import hoarelogic.
Require Import Zwf.
Require Import Wellfounded.

(** * Implementation of the expression language *)
Module Example <: ExprLang.

(** Here, I use only two global variables [VX] and [VY] of type [Z]
(binary integers). *)
Inductive ExVar: Type -> Type := 
  VX: (ExVar Z) | 
  VY: (ExVar Z). 

Definition Var:=ExVar.

(** An environment is just a pair of integers. First component
represents [VX] and second component represents [VY].  This is
expressed in [upd] and [get] below. *)
Definition Env:= (Z*Z)%type.

Definition upd (A:Type): (ExVar A) -> A -> Env -> Env :=
 fun x => 
   match x in (ExVar A) return A -> Env -> Env with
   | VX => fun vx e => (vx,snd e)
   | VY => fun vy e => (fst e,vy)
   end.

Definition get (A:Type): (ExVar A) -> Env -> A :=
 fun x => 
   match x in (ExVar A) return Env -> A with
   | VX => fun e => fst e
   | VY => fun e => snd e
   end.

(** I consider only two binary operators [PLUS] and [MINUS]. Their
meaning is given by [eval_binOP] below *)
Inductive binOP: Type := PLUS | MINUS.
 
Definition eval_binOP: binOP -> Z -> Z -> Z :=
 fun op => match op with
  | PLUS => Zplus
  | MINUS => Zminus
 end.

(** I consider only three comparison operators [EQ], [NEQ] and
[LE]. Their meaning is given by [eval_relOP] below *)
Inductive relOP: Type := EQ | NEQ | LE.

Definition eval_relOP: relOP -> Z -> Z -> bool :=
 fun op => match op with
  | EQ => Zeq_bool
  | NEQ => Zneq_bool
  | LE => Zle_bool
 end. 

(** Here is the abstract syntax of expressions. The semantics is given
by [eval] below *)
Inductive ExExpr: Type -> Type :=
 | const: forall (A:Type), A -> (ExExpr A)
 | binop: binOP -> (ExExpr Z) -> (ExExpr Z) -> (ExExpr Z)
 | relop: relOP -> (ExExpr Z) -> (ExExpr Z) -> (ExExpr bool)
 | getvar: forall (A:Type), (ExVar A) -> (ExExpr A). 

Definition Expr:= ExExpr.

Fixpoint eval (A:Type) (expr:Expr A) (e:Env) { struct expr } : A :=
 match expr in ExExpr A return A with
 | const A v => v
 | binop op e1 e2 => eval_binOP op (eval e1 e) (eval e2 e)
 | relop op e1 e2 => eval_relOP op (eval e1 e) (eval e2 e)
 | getvar A x => (get x e)
end.

End Example.

(** * Instantiation of the Hoare logic on this langage. *)
Module HL :=  HoareLogic(Example).
Import HL.
Import Example.

(** These coercions makes the abstract syntax more user-friendly *)
Coercion getvar: ExVar >-> ExExpr.
Coercion binop: binOP >-> Funclass.
Coercion relop: relOP >-> Funclass.

(** A last coercion useful for assertions *)
Coercion get: ExVar >-> Funclass.

(** ** A [gcd] computation in this language *)
Definition gcd := 
  (Iwhile (NEQ VX VY)
          (Iif (LE VX VY)
               (Iset VY (MINUS VY VX))
               (Iset VX (MINUS VX VY)))).

(** A small technical lemma on the mathematical notion of gcd (called
[Zis_gcd]) *)
Lemma Zgcd_minus: forall a b d:Z, Zis_gcd a (b - a) d -> Zis_gcd a b d.
Proof.
  intros a b d H; case H; constructor; intuition (auto with zarith).
  replace b with (b-a+a)%Z.
  auto with zarith.
  omega.
Qed.

Hint Resolve Zgcd_minus: zarith.

(** Two other lemmas relating [Zneq_bool] function with inequality
relation *)
Lemma Zneq_bool_false: forall x y, Zneq_bool x y=false -> x=y.
Proof.
 intros x y H0; apply Zcompare_Eq_eq; generalize H0; clear H0; unfold Zneq_bool. case (x ?= y)%Z; auto; 
 try (intros; discriminate); auto. 
Qed.

Lemma Zneq_bool_true: forall x y, Zneq_bool x y=true -> x<>y.
Proof.
 intros x y; unfold Zneq_bool.
 intros H H0; subst.
 rewrite Zcompare_refl in H.
 discriminate.
Qed.

Hint Resolve Zneq_bool_true Zneq_bool_false Zle_bool_imp_le Zis_gcd_intro: zarith.

(** ** Partial correctness proof of [gcd] *)
Lemma gcd_partial_proof: 
 forall x0 y0, (fun e => (VX e)=x0 /\ (VY e)=y0) 
   |= gcd  {= fun e => (Zis_gcd x0 y0 (VX e)) =}.
Proof.
 intros x0 y0. 
 apply PHL.soundness.
 simpl.
 intros e; intuition subst.
 (** after PO generation, I provide the invariant and simplify the goal *) 
 constructor 1 with (x:=fun e'=> 
  forall d, (Zis_gcd (VX e') (VY e') d)
              ->(Zis_gcd (VX e) (VY e) d)); simpl.
 intuition auto with zarith.
 (** - invariant => postcondition *)
 cutrewrite <- ((fst e')=(snd e')) in H; auto with zarith.
Qed.


(** ** Total correctness proof of [gcd] *)

Lemma gcd_total_proof: 
 forall x0 y0, (fun e => (VX e)=x0 /\ (VY e)=y0 /\ x0 > 0 /\ y0 > 0)
  |= gcd  [= fun e => (Zis_gcd x0 y0 (VX e)) =].
Proof.
 intros x0 y0. 
 apply THL.soundness.
 simpl.
 intros e; intuition subst.
 (** after simplification, I provide the invariant and then the variant *) 
 constructor 1 with (x:=fun e' => (VX e') > 0 /\ (VY e') > 0 /\
  forall d, (Zis_gcd (VX e') (VY e') d)
              ->(Zis_gcd (VX e) (VY e) d)); simpl.
 constructor 1 with (x:=fun e1 e0 => Zwf 0 ((VX e1)+(VY e1)) ((VX e0)+(VY e0))).
 (** - proof that my variant is a well_founded relation *) 
 constructor 1.
 apply wf_inverse_image with (f:=fun e=>(VX e)+(VY e)).
 auto with datatypes.
 (** - other goals *)
  unfold Zwf; simpl; (intuition auto with zarith).
 (** -- invariant => postcondition 
      --- gcd part like in partial correctness proof 
 *)
  cutrewrite <- ((fst e')=(snd e')) in H5; auto with zarith.
  (** --- new VY in branch "then" is positive *)
  cut ((fst e')<=(snd e')); auto with zarith.
  cut ((fst e')<>(snd e')); auto with zarith.
  (** --- new VX in branch "else" is positive *)
  cut (~(fst e')<=(snd e')); auto with zarith.
  intros X; rewrite (Zle_imp_le_bool _ _ X) in H4.
  discriminate.
Qed.

(** ** Another example: infinite loops in partial correctness.

Basic Hoare logic is not well-suited for reasoning about non-terminating programs.
In total correctness, postconditions of non-terminating programs are not provable.
In partial correctness, a non-terminating program satisfies any (unsatisfiable) postcondition.

For example, in an informal "meaning", the program below enumerates all multiples of 3. But this meaning 
can not be expressed here (even in partial correctness).
*)

Definition enum_3N := 
  (Iseq (Iset VX (const 0))
        (Iwhile (const true)
                (Iset VX (PLUS VX (const 3))))).

Lemma enum_3N_stupid: 
 (fun e => True) |= enum_3N  {= fun e => False =}.
Proof.
 apply PHL.soundness.
 simpl.
 constructor 1 with (x:=fun _:Env => True).
 intuition (discriminate || auto).
Qed.


(** "Tutorial on Hoare Logic" Library. Copyright 2007 Sylvain Boulme.

This file is distributed under the terms of the 
 "GNU LESSER GENERAL PUBLIC LICENSE" version 3.  
*)
