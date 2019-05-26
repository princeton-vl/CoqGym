(*
Copyright 2010 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

From Coq Require Import ssreflect ssrbool ssrfun Setoid.
From mathcomp Require Import seq.
Set Implicit Arguments.
Unset Strict Implicit. 
Unset Printing Implicit Defensive. 
Set Warnings "-projection-no-head-constant".

(******************************************************************************)
(* This file re-implements some of ssrbool's entities in Prop universe        *)
(******************************************************************************)

Lemma andTp p : True /\ p <-> p.      Proof. by intuition. Qed.
Lemma andpT p : p /\ True <-> p.      Proof. by intuition. Qed.  
Lemma andFp p : False /\ p <-> False. Proof. by intuition. Qed.
Lemma andpF p : p /\ False <-> False. Proof. by intuition. Qed.
Lemma orTp p : True \/ p <-> True.    Proof. by intuition. Qed.
Lemma orpT p : p \/ True <-> True.    Proof. by intuition. Qed.  
Lemma orFp p : False \/ p <-> p.      Proof. by intuition. Qed.
Lemma orpF p : p \/ False <-> p.      Proof. by intuition. Qed.

Delimit Scope rel_scope with rel.
Open Scope rel_scope.

(**************************************************************************)
(* We follow ssrbool, and provide four different types of predicates.     *)
(*                                                                        *)
(* (1) Pred is the type of propositional functions                        *)
(* (2) Simpl_Pred is the type of predicates that automatically simplify   *)
(*     when used in an applicative position.                              *)
(* (3) Mem_Pred is for predicates that support infix notation x \In P     *) 
(* (4) PredType is the structure for interpreting various types, such as  *)
(* lists, tuples, etc. as predicates.                                     *)
(*                                                                        *)
(* Important point is that custom lemmas over predicates can be stated in *)
(* terms of Pred, while Simpl_Pred, Mem_Pred and PredType are for         *)
(* technical developments used in this file only. More on this point      *)
(* can be found in ssrbool.                                               *)
(**************************************************************************)

Definition Pred T := T -> Prop.
Identity Coercion fun_of_Pred : Pred >-> Funclass.

Notation xPred0 := (fun _ => False).
Notation xPred1 := (fun x y => x = y).
Notation xPredT := (fun _ => True).
Notation xPredI := (fun (p1 p2 : Pred _) x => p1 x /\ p2 x).
Notation xPredU := (fun (p1 p2 : Pred _) x => p1 x \/ p2 x).
Notation xPredC := (fun (p : Pred _) x => ~ p x).
Notation xPredD := (fun (p1 p2 : Pred _) x => ~ p2 x /\ p1 x).
Notation xPreim := (fun f (p : Pred _) x => p (f x)).

Section Predicates.
Variable T : Type.

(* simple predicates *)

Definition Simpl_Pred := simpl_fun T Prop.
Definition SimplPred (p : Pred T) : Simpl_Pred := SimplFun p.
Coercion Pred_of_Simpl (p : Simpl_Pred) : Pred T := p : T -> Prop.

(* it's useful to declare the operations as simple predicates, so that *)
(* complex expressions automatically reduce when used in applicative   *)
(* positions *)

Definition Pred0 := SimplPred xPred0.
Definition Pred1 x := SimplPred (xPred1 x).
Definition PredT := SimplPred xPredT.
Definition PredI p1 p2 := SimplPred (xPredI p1 p2).
Definition PredU p1 p2 := SimplPred (xPredU p1 p2).
Definition PredC p := SimplPred (xPredC p).
Definition PredD p1 p2 := SimplPred (xPredD p1 p2).
Definition Preim rT f (d : Pred rT) := SimplPred (xPreim f d).

(* membership predicates *)

CoInductive Mem_Pred : Type := MemProp of Pred T.
Definition isMem pT toPred mem := mem = (fun p : pT => MemProp [eta toPred p]).

(* the general structure for predicates *)

Structure PredType : Type := PropPredType {
  Pred_Sort :> Type; 
  toPred : Pred_Sort -> Pred T; 
  _ : {mem | isMem toPred mem}}.

Definition mkPredType pT toP :=
  PropPredType (exist (@isMem pT toP) _ (erefl _)).

(* Pred, SimplPred, Mem_Pred, pred and simpl_pred are PredType's *)
Canonical Structure PredPredType := Eval hnf in @mkPredType (Pred T) id.
Canonical Structure SimplPredPredType := Eval hnf in mkPredType Pred_of_Simpl.
Coercion Pred_of_Mem mp : Pred_Sort PredPredType :=
  let: MemProp p := mp in [eta p].
Canonical Structure MemPredType := Eval hnf in mkPredType Pred_of_Mem.
Canonical Structure predPredType := Eval hnf in @mkPredType (pred T) id.
Canonical Structure simplpredPredType := 
  Eval hnf in @mkPredType (simpl_pred T) (fun p x => p x).

End Predicates.

Arguments Pred0 [T].
Arguments PredT [T].
Prenex Implicits Pred0 PredT PredI PredU PredC PredD Preim.

Notation "r1 +p r2" := (PredU r1 r2 : Pred _) 
  (at level 55, right associativity) : rel_scope.
Notation "r1 *p r2" := (xPredI r1 r2 : Pred _) 
  (at level 45, right associativity) : rel_scope.

Notation "[ 'Pred' : T | E ]" := (SimplPred (fun _ : T => E))
  (at level 0, format "[ 'Pred' :  T  |  E ]") : fun_scope.
Notation "[ 'Pred' x | E ]" := (SimplPred (fun x => E))
  (at level 0, x ident, format "[ 'Pred'  x  |  E ]") : fun_scope.
Notation "[ 'Pred' x : T | E ]" := (SimplPred (fun x : T => E))
  (at level 0, x ident, only parsing) : fun_scope.
Notation "[ 'Pred' x y | E ]" := (SimplPred (fun t => let: (x, y) := t in E))
  (at level 0, x ident, y ident, format "[ 'Pred'  x  y  |  E ]") : fun_scope.
Notation "[ 'Pred' x y : T | E ]" := 
  (SimplPred (fun t : (T*T) => let: (x, y) := t in E))
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Definition repack_Pred T pT :=
  let: PropPredType _ a mP := pT return {type of @PropPredType T for pT} -> _ in
   fun k => k a mP.

Notation "[ 'PredType' 'of' T ]" := (repack_Pred (fun a => @PropPredType _ T a))
  (at level 0, format "[ 'PredType'  'of'  T ]") : form_scope.

Notation Pred_Class := (Pred_Sort (PredPredType _)).
Coercion Sort_of_Simpl_Pred T (p : Simpl_Pred T) : Pred_Class := p : Pred T.

Definition PredArgType := Type.
Coercion Pred_of_argType (T : PredArgType) : Simpl_Pred T := PredT.

Notation "{ :: T }" := (T%type : PredArgType)
  (at level 0, format "{ ::  T }") : type_scope.

(* These must be defined outside a Section because "cooking" kills the *)
(* nosimpl tag. *)
Definition Mem T (pT : PredType T) : pT -> Mem_Pred T :=
  nosimpl (let: PropPredType _ _ (exist mem _) := pT return pT -> _ in mem).
Definition InMem T x mp := nosimpl Pred_of_Mem T mp x.

Prenex Implicits Mem.

(* Membership Predicates can be used as simple ones *)
Coercion Pred_of_Mem_Pred T mp := [Pred x : T | InMem x mp].

(* equality and subset *)

Definition EqPredType T (pT : PredType T) (p1 p2 : pT) := 
  forall x : T, toPred p1 x <-> toPred p2 x.

Definition SubPredType T (pT : PredType T) (p1 p2 : pT) := 
  forall x : T, toPred p1 x -> toPred p2 x.

Definition EqSimplPred T (p1 p2 : Simpl_Pred T) := EqPredType p1 p2.
Definition SubSimplPred T (p1 p2 : Simpl_Pred T) := SubPredType p1 p2.

Definition EqPredFun T1 T2 (pT2 : PredType T2) p1 p2 := 
  forall x : T1, @EqPredType T2 pT2 (p1 x) (p2 x).
Definition SubPredFun T1 T2 (pT2 : PredType T2) p1 p2 := 
  forall x : T1, @SubPredType T2 pT2 (p1 x) (p2 x).

Definition EqMem T p1 p2 := forall x : T, InMem x p1 <-> InMem x p2.
Definition SubMem T p1 p2 := forall x : T, InMem x p1 -> InMem x p2.

Notation "A <~> B" := (@EqPredType _ _ A B) 
  (at level 70, no associativity) : rel_scope.
Notation "A ~> B" := (@SubPredType _ _ A B) 
  (at level 70, no associativity) : rel_scope.
Notation "A <~1> B" := (@EqPredFun _ _ _ A B) 
  (at level 70, no associativity) : rel_scope.
Notation "A ~1> B" := (@SubPredFun _ _ _ A B) 
  (at level 70, no associativity) : rel_scope.

Notation "x \In A" := (InMem x (Mem A)) 
  (at level 70, no associativity) : rel_scope.
Notation "x \Notin A" := (~ (x \In A)) 
  (at level 70, no associativity) : rel_scope.
Notation "A =p B" := (EqMem (Mem A) (Mem B)) 
  (at level 70, no associativity) : type_scope.
Notation "A <=p B" := (SubMem (Mem A) (Mem B))  
  (at level 70, no associativity) : type_scope.

(* Some notation for turning PredTypes into Pred or Simple Pred *)
Notation "[ 'Mem' A ]" := (Pred_of_Simpl (Pred_of_Mem_Pred (Mem A)))
  (at level 0, only parsing) : fun_scope.
Notation "[ 'PredI' A & B ]" := (PredI [Mem A] [Mem B])
  (at level 0, format "[ 'PredI'  A  &  B ]") : fun_scope.
Notation "[ 'PredU' A & B ]" := (PredU [Mem A] [Mem B])
  (at level 0, format "[ 'PredU'  A  &  B ]") : fun_scope.
Notation "[ 'PredD' A & B ]" := (PredD [Mem A] [Mem B])
  (at level 0, format "[ 'PredD'  A  &  B ]") : fun_scope.
Notation "[ 'PredC' A ]" := (PredC [Mem A])
  (at level 0, format "[ 'PredC'  A ]") : fun_scope.
Notation "[ 'Preim' f 'of' A ]" := (Preim f [Mem A])
  (at level 0, format "[ 'Preim'  f  'of'  A ]") : fun_scope.

Notation "[ 'Pred' x \In A ]" := [Pred x | x \In A]
  (at level 0, x ident, format "[ 'Pred'  x  \In  A ]") : fun_scope.
Notation "[ 'Pred' x \In A | E ]" := [Pred x | (x \In A) /\ E]
  (at level 0, x ident, format "[ 'Pred'  x  \In  A  |  E ]") : fun_scope.
Notation "[ 'Pred' x y \In A & B | E ]" :=
  [Pred x y | (x \In A) /\ (y \In B) /\ E]
  (at level 0, x ident, y ident,
   format "[ 'Pred'  x  y  \In  A  &  B  |  E ]") : fun_scope.
Notation "[ 'Pred' x y \In A & B ]" := [Pred x y | (x \In A) /\ (y \In B)]
  (at level 0, x ident, y ident,
   format "[ 'Pred'  x  y  \In  A  &  B ]") : fun_scope.
Notation "[ 'Pred' x y \In A | E ]" := [Pred x y \In A & A | E]
  (at level 0, x ident, y ident,
   format "[ 'Pred'  x  y  \In  A  |  E ]") : fun_scope.
Notation "[ 'Pred' x y \In A ]" := [Pred x y \In A & A]
  (at level 0, x ident, y ident,
   format "[ 'Pred'  x  y  \In  A ]") : fun_scope.

Section Simplifications. 
Variables (T : Type) (pT : PredType T).

Lemma Mem_toPred : forall (p : pT), Mem (toPred p) = Mem p.
Proof. by rewrite /Mem; case: pT => T1 app1 [mem1  /= ->]. Qed.

Lemma toPredE x (p : pT) : toPred p x = (x \In p).
Proof. by rewrite -Mem_toPred. Qed.

Lemma In_Simpl x (p : Simpl_Pred T) : (x \In p) = p x.
Proof. by []. Qed.

Lemma Simpl_PredE (p : Pred T) : p <~> [Pred x | p x].
Proof. by []. Qed.

Lemma Mem_Simpl (p : Simpl_Pred T) : Mem p = p :> Pred T.
Proof. by []. Qed.

Definition MemE := Mem_Simpl. (* could be extended *)

Lemma Mem_Mem (p : pT) : (Mem (Mem p) = Mem p) * (Mem [Mem p] = Mem p).
Proof. by rewrite -Mem_toPred. Qed.

End Simplifications. 

(**************************************)
(* Definitions and lemmas for setoids *)
(**************************************)

Section RelProperties.
Variables (T : Type) (pT : PredType T).

Lemma EqPredType_refl (r : pT) : EqPredType r r. Proof. by []. Qed.
Lemma SubPredType_refl (r : pT) : SubPredType r r. Proof. by []. Qed.  

Lemma EqPredType_sym (r1 r2 : pT) : EqPredType r1 r2 -> EqPredType r2 r1.
Proof. by move=>H1 x; split; move/H1. Qed.

Lemma EqPredType_trans' (r1 r2 r3 : pT) : 
  EqPredType r1 r2 -> EqPredType r2 r3 -> EqPredType r1 r3.
Proof. by move=>H1 H2 x; split; [move/H1; move/H2 | move/H2; move/H1]. Qed.
 
Lemma SubPredType_trans' (r1 r2 r3 : pT) : 
  SubPredType r1 r2 -> SubPredType r2 r3 -> SubPredType r1 r3.
Proof. by move=>H1 H2 x; move/H1; move/H2. Qed. 

Definition EqPredType_trans r2 r1 r3 := @EqPredType_trans' r1 r2 r3. 
Definition SubPredType_trans r2 r1 r3 := @SubPredType_trans' r1 r2 r3.
End RelProperties.

Hint Resolve EqPredType_refl SubPredType_refl : core.

(* Declaration of relations *)

Add Parametric Relation T (pT : PredType T) : pT (@EqPredType _ pT)    
   reflexivity proved by (@EqPredType_refl _ _)                         
  symmetry proved by (@EqPredType_sym _ _)                              
  transitivity proved by (@EqPredType_trans' _ _) as EqPredType_rel.    

Add Parametric Relation T : (Simpl_Pred T) (@EqSimplPred _)
  reflexivity proved by (@EqPredType_refl _ _)
  symmetry proved by (@EqPredType_sym _ _)
  transitivity proved by (@EqPredType_trans' _ _) as EqSimplPred_rel.

Add Parametric Relation T : (Simpl_Pred T) (@SubSimplPred _) 
  reflexivity proved by (@SubPredType_refl _ _)
  transitivity proved by (@SubPredType_trans' _ _) as SubSimplPred_rel.

Add Parametric Relation T : (Mem_Pred T) (@EqMem T)
  reflexivity proved by (@EqPredType_refl _ _)
  symmetry proved by (@EqPredType_sym _ _)
  transitivity proved by (@EqPredType_trans' _ _) as EqMem_rel.

Add Parametric Relation T : (Mem_Pred T) (@SubMem _) 
  reflexivity proved by (@SubPredType_refl _ _)
  transitivity proved by (@SubPredType_trans' _ _) as SubMem_rel.

(* Declaring morphisms. *)

Add Parametric Morphism T : (@Pred_of_Simpl T) with signature
      @EqSimplPred _ ==> @EqPredType T (PredPredType T) as Pred_of_Simpl_morph. 
Proof. by []. Qed.

Add Parametric Morphism T (pT : PredType T) : (@EqPredType T pT) with signature 
    @EqPredType _ _ ==> @EqPredType _ _ ==> iff as EqPredType_morph.
Proof. by move=>r1 s1 H1 r2 s2 H2; rewrite H1 H2. Qed.

Add Parametric Morphism T (pT : PredType T) : (@SubPredType T pT) with signature
    @EqPredType _ _ ==> @EqPredType _ _ ==> iff as SubPred_morph.
Proof. by move=>r1 s1 H1 r2 s2 H2; split=>H x; move/H1; move/H; move/H2. Qed.

Add Parametric Morphism T : (@InMem T) with signature 
    @eq _ ==> @EqMem _ ==> iff as InMem_morph.
Proof. by move=>x r s H; split; move/H. Qed.

Add Parametric Morphism T (pT : PredType T) : (@Mem T pT) with signature
  @EqPredType _ _ ==> @EqMem _ as Mem_morhp.
Proof. by move=>x y H p; rewrite /EqPredType -!toPredE in H *; rewrite H. Qed.

Add Parametric Morphism T : (@PredU T) with signature 
    @EqPredType _ _ ==> @EqPredType _ _ ==> @EqSimplPred _ as predU_morph.
Proof.
move=>r1 s1 H1 r2 h2 H2 x; split; 
by case; [move/H1 | move/H2]=>/=; auto.
Qed.

Add Parametric Morphism T : (@PredI T) with signature 
    @EqPredType _ _ ==> @EqPredType _ _ ==> @EqPredType _ _ as predI_morph.
Proof.
move=>r1 s1 H1 r2 s2 H2 x; split; 
by case; move/H1=>T1; move/H2=>T2.
Qed.

Add Parametric Morphism T : (@PredC T) with signature 
    @EqPredType _ _ ==> @EqPredType _ _ as predC_morph.
Proof. by move=>r s H x; split=>H1; apply/H. Qed.

Section RelLaws.
Variable (T : Type).

Lemma orrI (r : Pred nat) : r +p r <~> r.
Proof.  by move=>x; split; [case | left]. Qed.

Lemma orrC (r1 r2 : Pred T) : r1 +p r2 <~> r2 +p r1.
Proof. move=>x; split=>/=; tauto. Qed. 

Lemma orr0 (r : Pred T) : r +p Pred0 <~> r.
Proof. by move=>x; split; [case | left]. Qed.

Lemma or0r (r : Pred T) : Pred0 +p r <~> r.
Proof. by rewrite orrC orr0. Qed.

Lemma orrCA (r1 r2 r3 : Pred T) : r1 +p r2 +p r3 <~> r2 +p r1 +p r3.
Proof. by move=>x; split=>/=; intuition. Qed.

Lemma orrAC (r1 r2 r3 : Pred T) : (r1 +p r2) +p r3 <~> (r1 +p r3) +p r2.
Proof. by move=>?; split=>/=; intuition. Qed.

Lemma orrA (r1 r2 r3 : Pred T) : (r1 +p r2) +p r3 <~> r1 +p r2 +p r3.
Proof. by rewrite (orrC r2) orrCA orrC. Qed.

(* absorption *)
Lemma orrAb (r1 a : Pred T) : r1 <~> r1 +p a <-> a ~> r1. 
Proof.
split; first by move=>-> x /=; auto.
move=>H x /=; split; first by auto.
by case=>//; move/H.
Qed.

Lemma sub_orl (r1 r2 : Pred T) : r1 ~> r1 +p r2. Proof. by left. Qed.
Lemma sub_orr (r1 r2 : Pred T) : r2 ~> r1 +p r2. Proof. by right. Qed.   

End RelLaws.

Section SubMemLaws.
Variable T : Type.

Lemma subp_refl (p : Pred T) : p <=p p.
Proof. by []. Qed.

Lemma subp_asym (p1 p2 : Pred T) : p1 <=p p2 -> p2 <=p p1 -> p1 =p p2.
Proof. by move=>H1 H2 x; split; [move/H1 | move/H2]. Qed.

Lemma subp_trans (p2 p1 p3 : Pred T) : p1 <=p p2 -> p2 <=p p3 -> p1 <=p p3.
Proof. by move=>H1 H2 x; move/H1; move/H2. Qed.

Lemma subp_or (p1 p2 q : Pred T) : p1 <=p q /\ p2 <=p q <-> p1 +p p2 <=p q.
Proof. 
split=>[[H1] H2 x|H1]; first by case; [move/H1 | move/H2].
by split=>x H2; apply: H1; [left | right].
Qed.

Lemma subp_and (p1 p2 q : Pred T) : q <=p p1 /\ q <=p p2 <-> q <=p p1 *p p2.
Proof.
split=>[[H1] H2 x|] H; last by split=>x; case/H.
by split; [apply: H1 | apply: H2].
Qed.

Lemma subp_orl (p1 p2 q : Pred T) : p1 <=p p2 -> p1 +p q <=p p2 +p q.
Proof. by move=>H x; case; [move/H; left|right]. Qed.

Lemma subp_orr (p1 p2 q : Pred T) : p1 <=p p2 -> q +p p1 <=p q +p p2.
Proof. by move=>H x; case; [left | move/H; right]. Qed.

Lemma subp_andl (p1 p2 q : Pred T) : p1 <=p p2 -> p1 *p q <=p p2 *p q.
Proof. by by move=>H x [H1 H2]; split; [apply: H|]. Qed.

Lemma subp_andr (p1 p2 q : Pred T) : p1 <=p p2 -> q *p p1 <=p q *p p2.
Proof. by move=>H x [H1 H2]; split; [|apply: H]. Qed.

End SubMemLaws.

Hint Resolve subp_refl : core.

Section ListMembership.
Variable T : Type.

Fixpoint Mem_Seq (s : seq T) :=
  if s is y::s' then (fun x => x = y \/ Mem_Seq s' x) else xPred0.

Definition EqSeq_Class := seq T.
Identity Coercion seq_of_EqSeq : EqSeq_Class >-> seq.

Coercion Pred_of_Eq_Seq (s : EqSeq_Class) : Pred_Class := [eta Mem_Seq s].

Canonical Structure seq_PredType := @mkPredType T (seq T) Pred_of_Eq_Seq.
(* The line below makes Mem_Seq a canonical instance of topred. *) 
Canonical Structure Mem_Seq_PredType := mkPredType Mem_Seq.

Lemma In_cons y s x : (x \In y :: s) <-> (x = y) \/ (x \In s).
Proof. by []. Qed.

Lemma In_nil x : (x \In [::]) <-> False.
Proof. by []. Qed.

Lemma Mem_Seq1 x y : (x \In [:: y]) <-> (x = y).
Proof. by rewrite In_cons orpF. Qed.

Definition InE := (Mem_Seq1, In_cons, In_Simpl).

Lemma Mem_cat x : forall s1 s2, (x \In s1 ++ s2) <-> x \In s1 \/ x \In s2.
Proof.
elim=>[|y s1 IH] s2 /=; first by split; [right | case].
rewrite !InE /=.
split.
- case=>[->|/IH]; first by left; left. 
  by case; [left; right | right]. 
case; first by case; [left | move=>H; right; apply/IH; left]. 
by move=>H; right; apply/IH; right. 
Qed.

Lemma In_split x s : x \In s -> exists s1 s2, s = s1 ++ x :: s2.
Proof.
elim:s=>[|y s IH] //=; rewrite InE.
case=>[<-|]; first by exists [::], s.
by case/IH=>s1 [s2 ->]; exists (y :: s1), s2.
Qed.

End ListMembership.

Lemma Mem_map T T' (f : T -> T') x (s : seq T) : 
         x \In s -> f x \In (map f s).
Proof.
elim: s=>[|y s IH] //; rewrite InE /=.
by case=>[<-|/IH]; [left | right].
Qed.

Lemma Mem_map_inv T T' (f : T -> T') x (s : seq T) : 
        x \In (map f s) -> exists y, x = f y /\ y \In s.
Proof.
elim: s=>[|y s IH] //=; rewrite InE /=.
case; first by move=>->; exists y; split=>//; left. 
by case/IH=>z [->]; exists z; split=>//; right. 
Qed.

Prenex Implicits Mem_map_inv.

(* Setoids for extensional equality of functions *)

Lemma eqfun_refl A B (f : A -> B) : f =1 f. Proof. by []. Qed.
Lemma eqfun_sym A B (f1 f2 : A -> B) : f1 =1 f2 -> f2 =1 f1. 
Proof. by move=>H x; rewrite H. Qed.
Lemma eqfun_trans A B (f1 f2 f3 : A -> B) : f1 =1 f2 -> f2 =1 f3 -> f1 =1 f3.
Proof. by move=>H1 H2 x; rewrite H1 H2. Qed.

Add Parametric Relation A B : (A -> B) (@eqfun _ _)
  reflexivity proved by (@eqfun_refl A B)
  symmetry proved by (@eqfun_sym A B)
  transitivity proved by (@eqfun_trans A B) as eqfun_morph.


(***********************************)
(* Image of a collective predicate *)
(***********************************)

Section Image.
Variables (A B : Type) (P : Pred A) (f : A -> B).

Inductive image_spec b : Prop := Im_mem a of b = f a & a \In P.

Definition Image' : Pred B := image_spec. 

End Image. 

(* swap to make the notation consider P before E; helps inference *)
Notation Image f P := (Image' P f).

Notation "[ 'Image' E | i <- s ]" := (Image (fun i => E) s)
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'Image'  E '/ '  |  i  <-  s ] ']'") : rel_scope.

Notation "[ 'Image' E | i <- s & C ]" := [Image E | i <- [PredI s & C]]
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'Image'  E '/ '  |  i  <-  s '/ '  &  C ] ']'") : rel_scope.

Notation "[ 'Image' E | i : T <- s ]" := (Image (fun i : T => E) s)
  (at level 0, E at level 99, i ident, only parsing) : rel_scope.

Notation "[ 'Image' E | i : T <- s & C ]" :=
  [Image E | i : T <- [PredI s & C]]
  (at level 0, E at level 99, i ident, only parsing) : rel_scope.

Lemma Image_mem A B (f : A -> B) (P : Pred A) x : x \In P -> f x \In Image f P.
Proof. by apply: Im_mem. Qed.

Lemma Image_inj_sub A B (f : A -> B) (X1 X2 : Pred A) : 
        injective f -> Image f X1 <=p Image f X2 -> X1 <=p X2.
Proof. by move=>H E x /(Image_mem f) /E [y] /H ->. Qed.

Lemma Image_inj_eqmem A B (f : A -> B) (X1 X2 : Pred A) : 
        injective f -> Image f X1 =p Image f X2 -> X1 =p X2.
Proof. by move=>H E; split; apply: Image_inj_sub H _ _; rewrite E. Qed.

Lemma ImageU A B (f : A -> B) (X1 X2 : Pred A) : 
        Image f (PredU X1 X2) =p [PredU Image f X1 & Image f X2].
Proof.
move=>x; split.
- by case=>y -> [H|H]; [left | right]; apply: Image_mem. 
by case; case=>y -> H; apply: Image_mem; [left | right]. 
Qed.

Lemma ImageIm A B C (f1 : B -> C) (f2 : A -> B) (X : Pred A) : 
        Image f1 (Image f2 X) =p Image (f1 \o f2) X. 
Proof.
move=>x; split; first by case=>_ -> [x' ->] H; exists x'.
by case=>a -> H; exists (f2 a)=>//; exists a.
Qed.

Lemma ImageEq A B (f1 f2 : A -> B) (X : Pred A) : 
        f1 =1 f2 -> Image f1 X =p Image f2 X.
Proof. by move=>H x; split; case=>a ->; exists a. Qed.

