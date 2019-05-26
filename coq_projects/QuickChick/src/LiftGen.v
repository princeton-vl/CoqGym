
Require Import RandomQC GenLow.

Import GenLow.

Inductive vec A : nat -> Type :=
  | nil : vec A 0
  | cons : forall {n:nat}, A -> vec A n -> vec A (S n).

Definition vapp {A}{n}{p} (v:vec A n) (w:vec A p) : vec A (n+p).
induction v. apply w. simpl.
apply cons. apply a. apply IHv.
Defined.
(* or course ... this would have been too easy
Fixpoint vapp {A}{n}{p} (v:vec A n) (w:vec A p) : vec A (n+p) :=
  match v with
  | nil => w
  | cons _ a v' => cons a (vapp v' w)
  end.
*)

Fixpoint tvec_to_fun {n} (v : vec Type n) (t:Type) (f : Type -> Type) : Type :=
  match v with
  | nil => t
  | cons _ X v' => f X -> tvec_to_fun v' t f
  end.

Fixpoint tvec_to_prod {n} (v : vec Type n) : Type :=
  match v with
  | nil => unit
  | cons _ X v' => prod X (tvec_to_prod v')
  end.

Definition applyN {n:nat} {As : vec Type n} {B : Type}
  (F : tvec_to_fun As B id) (vs : tvec_to_prod As) : B.
induction As as [| n A1 As']; simpl in *. exact F.
destruct vs as [v vs']. info_eauto.
Defined. Print applyN.

(* of course writing terms is a pain ... it's Coq
Fixpoint applyN {n:nat} {As : vec Type n} {B : Type}
    (F : tvec_to_fun As B id) (vs : tvec_to_prod As) : B :=
  match As with
  | nil => F
  | cons n A1 As' => let (v, vs') := vs in applyN (F v) vs'
  end.
*)

Definition liftGenN_aux : forall {n :nat} {As : vec Type n} {B : Type}
                                 (n':nat) (As': vec Type n') (vs : tvec_to_prod As')
             (F : tvec_to_fun (vapp As As') B id), tvec_to_fun As (G B) G.
induction As as [| n AH AsT]; intros; simpl in *. exact (returnGen (applyN F vs)).
intro m1. (* need to get to type G B before I can apply bindGen, need to curry? *)

(* eapply IHAsT. exact (cons vs) *)
(* eapply bindGen in m1. *)
(* refine (bindGen m1 (fun x1 => _)). *)

Admitted.

(* can't even write the lemma I need using homogenous equality
The term "v" has type "vec A n" while it is expected to have type
 "vec A (n + 0)".
Lemma vapp_nil : forall {A}{n} (v:vec A n),
  (vapp v (nil A)) = v.
*)

(* just a permutation of the above *)
Definition liftGenN_aux' :
  forall (n':nat) (As': vec Type n') (vs : tvec_to_prod As')
                        {n :nat} {As : vec Type n} {B : Type}
             (F : tvec_to_fun (vapp As As') B id), tvec_to_fun As (G B) G.
Admitted.

Definition liftGenN : forall {n:nat} {As : vec Type n} {B : Type}
    (F : tvec_to_fun As B id), tvec_to_fun As (G B) G.
  (* exact (liftGenN_aux 0 (nil Type) tt) -- needs a lemma *)
  intros. apply (liftGenN_aux' 0 (nil Type) tt).
Admitted.

(*
Definition liftGen5 {A1 A2 A3 A4 A5 R}
           (F : A1 -> A2 -> A3 -> A4 -> A5 -> R)
           (m1 : G A1) (m2 : G A2) (m3 : G A3) (m4: G A4) (m5 : G A5)
: G R := nosimpl(
  bindGen m1 (fun x1 =>
  bindGen m2 (fun x2 =>
  bindGen m3 (fun x3 =>
  bindGen m4 (fun x4 =>
  bindGen m5 (fun x5 =>
  returnGen (F x1 x2 x3 x4 x5))))))).

*)
