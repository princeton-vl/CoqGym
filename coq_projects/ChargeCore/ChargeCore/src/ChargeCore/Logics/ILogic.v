(*---------------------------------------------------------------------------
    This file axiomatises the inference rules of an intuitionistic logic and
    offers some parametric instances to make it straightforward to create a new
    logic that satisfies those axioms. The purpose is to factor out what the
    assertion logic and specification logic of a separation logic framework
    have in common.
  ---------------------------------------------------------------------------*)
Require Import Setoid Morphisms RelationClasses Program.Basics Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

(* The natural numbers in descending order. *)
Global Instance ge_Pre: PreOrder ge.
Proof. repeat constructor. hnf. eauto with arith. Qed.

(* These tactics are meant to relieve the user from remembering morphism names.
   In most cases they will apply the most general morphism for the arity
   requested. *)
(* TODO: move this somewhere more general. *)
Ltac postcancel := unfold Basics.flip; trivial.
Ltac cancel1 :=
  apply (proper_prf (Proper := _: Proper (_ ==> _) _));
  postcancel.
Ltac cancel2 :=
  apply (proper_prf (Proper := _: Proper (_ ==> _ ==> _) _));
  postcancel.
Ltac cancel3 :=
  apply (proper_prf (Proper := _: Proper (_ ==> _ ==> _ ==> _) _));
  postcancel.

Class Inhabited (A : Type) := { cinhabited : inhabited A}.

Instance inhabitedNat: Inhabited nat. Proof. split; split; apply 0. Qed.
Instance inhabitedBool: Inhabited bool. Proof. split; split; apply true. Qed.

(* Logical connectives *)
Class ILogicOps (A : Type) : Type := {
  lentails: A -> A -> Prop;
  ltrue: A;
  lfalse: A;
  limpl: A -> A -> A;
  land: A -> A -> A;
  lor: A -> A -> A;
  lforall: forall {T : Type}, (T -> A) -> A;
  lexists: forall {T : Type}, (T -> A) -> A
}.

(* These notations have to sit strictly between level 80 (precendence of /\)
   and level 70 (precedence of =). *)
Infix "|--"  := lentails (at level 80, no associativity).
Infix "//\\"   := land (at level 75, right associativity).
Infix "\\//"   := lor (at level 76, right associativity).
Infix "-->>"   := limpl (at level 77, right associativity).
Notation "'Forall' x : T , p" :=
  (lforall (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Forall' x , p" :=
  (lforall (fun x => p)) (at level 78, x ident, right associativity, only parsing).
Notation "'Exists' x : T , p" :=
  (lexists (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Exists' x , p" :=
  (lexists (fun x => p)) (at level 78, x ident, right associativity, only parsing).

Section ILogicEquiv.
  Context {A : Type} `{IL: ILogicOps A}.

  Definition lequiv P Q := P |-- Q /\ Q |-- P.
End ILogicEquiv.



Infix "-|-"  := lequiv (at level 85, no associativity).

(* Axioms of an intuitionistic logic, presented in a sequent calculus style
   with singleton contexts on the left of the turnstile. This form is
   particularly suited for the undisciplined context manipulation that tends to
   happen in separation logic.

   Every connective has a number of L-rules and a number of R-rules describing
   what can be done to prove a goal that has the connective as the head symbol
   of the left, respectively right, side of a turnstile. The notable exception
   to this pattern is implication, which is required to be the right adjoint of
   conjunction. This makes singleton contexts work. *)
Class ILogic {A : Type} {ILOps: ILogicOps A} : Type := {
  lentailsPre:> PreOrder lentails;
  ltrueR: forall (C : A), C |-- ltrue;
  lfalseL: forall (C : A), lfalse |-- C;
  lforallL: forall (T : Type) x (P: T -> A) C, P x |-- C -> lforall P |-- C;
  lforallR: forall (T : Type) (P: T -> A) C, (forall x, C |-- P x) -> C |-- lforall P;
  lexistsL: forall (T : Type) (P: T -> A) C, (forall x, P x |-- C) -> lexists P |-- C;
  lexistsR: forall (T : Type) (x : T) (P: T -> A) C, C |-- P x -> C |-- lexists P;
  landL1: forall (P Q C : A), P |-- C  ->  P //\\ Q |-- C;
  landL2: forall (P Q C : A), Q |-- C  ->  P //\\ Q |-- C;
  lorR1:  forall (P Q C : A), C |-- P  ->  C |-- P \\// Q;
  lorR2:  forall (P Q C : A), C |-- Q  ->  C |-- P \\// Q;
  landR:  forall (P Q C : A), C |-- P  ->  C |-- Q  ->  C |-- P //\\ Q;
  lorL:   forall (P Q C : A), P |-- C  ->  Q |-- C  ->  P \\// Q |-- C;
  landAdj: forall (P Q C : A), C |-- (P -->> Q) -> C //\\ P |-- Q;
  limplAdj: forall (P Q C : A), C //\\ P |-- Q -> C |-- (P -->> Q)
}.

Arguments ILogic _ {ILOps}.
Arguments lforallL {A ILOps ILogic} [T] x P C _.
Arguments lexistsR {A ILOps ILogic} [T] x P C _.

Notation "|--  P" := (ltrue |-- P) (at level 85, no associativity).
Hint Extern 0 (?x |-- ?x) => reflexivity.
Hint Extern 0 (_ |-- ltrue) => apply ltrueR.
Hint Extern 0 (lfalse |-- _) => apply lfalseL.
Hint Extern 0 (?P |-- ?Q) => (is_evar P; reflexivity) || (is_evar Q; reflexivity).

Section ILogicEquiv2.
  Context {A : Type} `{IL: ILogic A}.

  Global Instance lequivEquivalence : Equivalence lequiv.
  Proof.
    unfold lequiv. constructor; red.
    + split; reflexivity.
    + intuition.
    + intros P Q R [HPQ HQP] [HQR HRQ];
      split; etransitivity; eassumption.
  Qed.

End ILogicEquiv2.

(* Most of the connectives in ILogicOps are redundant. They can be derived from
   lexists, lforall and limpl, and the choice of limpl is unique up to lequiv
   since it is an adjoint. *)

Section ILogicEquivOps.
  Context {A : Type} `{IL: ILogic A}.

  Lemma land_is_forall P Q :
    P //\\ Q -|- Forall b : bool, if b then P else Q.
  Proof.
    split.
    - apply lforallR; intro x; destruct x.
      + apply landL1; reflexivity.
      + apply landL2; reflexivity.
    - apply landR.
      + apply lforallL with true; reflexivity.
      + apply lforallL with false; reflexivity.
  Qed.

  Lemma lor_is_exists P Q:
    P \\// Q -|- Exists b : bool, if b then P else Q.
  Proof.
    split.
    - apply lorL.
      + apply lexistsR with true; reflexivity.
      + apply lexistsR with false; reflexivity.
    - apply lexistsL; intro x; destruct x.
      + apply lorR1; reflexivity.
      + apply lorR2; reflexivity.
  Qed.

  Lemma ltrue_is_forall:
    ltrue -|- Forall x: Empty_set, Empty_set_rect _ x.
  Proof.
    split; [apply lforallR|]; intuition.
  Qed.

  Lemma lfalse_is_exists:
    lfalse -|- Exists x: Empty_set, Empty_set_rect _ x.
  Proof. split; [|apply lexistsL]; intuition. Qed.

End ILogicEquivOps.

Section ILogicMorphisms.
  Context {A T : Type} `{IL: ILogic A}.

  Global Instance lequiv_lentails : subrelation lequiv lentails.
  Proof. firstorder. Qed.
  Global Instance lequiv_flip_lentails: subrelation lequiv (flip lentails).
  Proof. firstorder. Qed.

  Global Instance lforall_lentails_m:
    Proper (pointwise_relation T lentails ++> lentails) lforall.
  Proof.
    intros P P' HP. apply lforallR; intro x;  apply lforallL with x.
    rewrite HP; reflexivity.
  Qed.

  Global Instance lforall_lequiv_m:
    Proper (pointwise_relation T lequiv ++> lequiv) lforall.
  Proof.
    intros P P' HP; split; apply lforall_lentails_m; intro x; apply HP.
  Qed.

  Global Instance lexists_lentails_m:
    Proper (pointwise_relation T lentails ++> lentails) lexists.
  Proof.
    intros P P' HP. apply lexistsL; intro x; apply lexistsR with x.
    rewrite HP; reflexivity.
  Qed.

  Global Instance lexists_lequiv_m:
    Proper (pointwise_relation T lequiv ++> lequiv) lexists.
  Proof.
    intros P P' HP; split; apply lexists_lentails_m; intro x; apply HP.
  Qed.

  Global Instance : Proper (lequiv ==> lequiv ==> iff) lequiv.
  Proof.
    intros P P' HP Q Q' HQ; split; intros H.
    + rewrite <- HP; rewrite <- HQ; assumption.
    + rewrite HP; rewrite HQ; assumption.
  Qed.

  Global Instance lequiv_lentails_m : Proper (lequiv ==> lequiv ==> iff) lentails.
  Proof.
    cbv; intuition; (etransitivity; [etransitivity|]); eassumption.
  Qed.

  Global Instance lentails_lentails_m: Proper (lentails --> lentails ++> impl) lentails.
  Proof.
    intuition.
  Qed.

  Global Instance land_lentails_m:
    Proper (lentails ++> lentails ++> lentails) land.
  Proof.
    intros P P' HP Q Q' HQ.
    apply landR; [apply landL1 | apply landL2]; assumption.
  Qed.

  Global Instance land_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) land.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply land_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lor_lentails_m:
    Proper (lentails ++> lentails ++> lentails) lor.
  Proof.
    intros P P' HP Q Q' HQ.
    apply lorL; [apply lorR1 | apply lorR2]; assumption.
  Qed.

  Global Instance lor_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lor.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lor_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance limpl_lentails_m:
    Proper (lentails --> lentails ++> lentails) limpl.
  Proof.
    intros P P' HP Q Q' HQ; red in HP.
    apply limplAdj; rewrite <- HQ, HP; apply landAdj; reflexivity.
  Qed.

  Global Instance limpl_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) limpl.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply limpl_lentails_m; (apply HP || apply HQ).
  Qed.

End ILogicMorphisms.

Hint Extern 0 (?x -|- ?x) => reflexivity.
Hint Extern 0 (?P -|- ?Q) => (is_evar P; reflexivity) || (is_evar Q; reflexivity).

(* TODO: also add lforwardR. *)
Lemma lforwardL {A} `{IL: ILogic A} {Q R}:
    Q |-- R -> forall P G,
    P |-- Q ->
    (P |-- R -> G) ->
    G.
Proof. intros HQR P G HPQ HG. apply HG. etransitivity; eassumption. Qed.

Tactic Notation "lforwardL" hyp(H) :=
  eapply (lforwardL H); clear H; [|intros H].

Section ILogicFacts.
  Context {A T : Type} `{IL: ILogic A}.

  (* Experiments with proof search. *)
  Ltac landR :=
    repeat match goal with
    | |- _ |-- _ //\\ _ => apply landR
    end.

  Ltac landL :=
    repeat match goal with
    | |- ?L1 //\\ ?L2 |-- ?R =>
        match L1 with
        | context [R] => apply landL1
        | _ =>
          match L2 with
          | context [R] => apply landL2
          end
        end
    end.
    
  Lemma lentails_refl P : P |-- P.
  Proof. reflexivity. Qed.

  Lemma landC P Q: P //\\ Q -|- Q //\\ P.
  Proof. split; landR; landL; reflexivity. Qed.

  Lemma landA P Q R: (P //\\ Q) //\\ R -|- P //\\ (Q //\\ R).
  Proof. split; landR; landL; reflexivity. Qed.

  Lemma lorC P Q : P \\// Q -|- Q \\// P.
  Proof.
    split; apply lorL; [apply lorR2 | apply lorR1 | apply lorR2 | apply lorR1]; reflexivity.
  Qed.

  Lemma lorA P Q R : (P \\// Q) \\// R -|- P \\// (Q \\// R).
  Proof.
  	split; apply lorL; try apply lorL; [
  	   apply lorR1 |
       apply lorR2; apply lorR1 |
       apply lorR2; apply lorR2 |
       apply lorR1; apply lorR1 |
       apply lorR1; apply lorR2 |
       apply lorR2
     ]; reflexivity.
   Qed.

  (* Special case of limplAdj/landAdj when there is just ltrue on the lhs *)
  Lemma limplValid P Q:
    |-- P -->> Q <->
    P |-- Q.
  Proof.
    split; intro H.
    - etransitivity; [eapply landR; [apply ltrueR|reflexivity]|].
      apply landAdj; assumption.
    - apply limplAdj. apply landL2; assumption.
  Qed.

  (* Left-rule for limpl. This breaks the discipline of the ILogic presentation
     since the implication is not strictly the top symbol of the left-hand side,
     but it remains a convenient rule. *)
  Lemma limplL P Q CL CR (HP: CL |-- P) (HR: Q //\\ CL |-- CR) :
    (P -->> Q) //\\ CL |-- CR.
  Proof.
    rewrite <-HR, <-HP. apply landR; [apply landAdj | apply landL2]; reflexivity.
  Qed.

  Lemma limplAdj2 P Q R : P -->> Q -->> R -|- P //\\ Q -->> R.
  Proof.
  	split.
  	+ apply limplAdj. do 2 (apply limplL; [landL; reflexivity|]).
  	  landL. reflexivity.
    + do 2 apply limplAdj; rewrite landA.
      apply limplL; [reflexivity | landL; reflexivity].
  Qed.

  Lemma landexistsDL1 (f : T -> A) (P : A) :
    lexists f //\\ P |-- Exists a, (f a //\\ P).
  Proof.
    apply landAdj; apply lexistsL; intro a;
    apply limplAdj; apply lexistsR with a; reflexivity.
  Qed.

  Lemma landexistsDL2 (f : T -> A) (P : A) :
    P //\\ lexists f |-- Exists a, (P //\\ f a).
  Proof.
    rewrite landC, landexistsDL1.
    setoid_rewrite landC at 1; reflexivity.
  Qed.
  
  Lemma landexistsDR1 (f : T -> A) (P : A) :
     Exists a, (f a //\\ P) |-- lexists f //\\ P.
  Proof.
    apply lexistsL; intro a; apply landR.
    - apply landL1; apply lexistsR with a; reflexivity.
    - apply landL2; reflexivity.
  Qed.

  Lemma landexistsDR2 (f : T -> A) (P : A) :
     Exists a, (P //\\ f a) |-- P //\\ lexists f.
  Proof.
    rewrite landC, <- landexistsDR1.
    setoid_rewrite landC at 1; reflexivity.
  Qed.
  
  Lemma landexistsD1 (f : T -> A) (P : A) :
    (Exists a, f a) //\\ P -|- Exists a, (f a //\\ P).
  Proof.
    split; [apply landexistsDL1 | apply landexistsDR1].
  Qed.


  Lemma lorexistsDL (f : T -> A) (P : A) {H : Inhabited T} :
    (Exists a, f a) \\// P |-- Exists a, (f a \\// P).
  Proof.
  	apply lorL.
	+ apply lexistsL; intro x; apply lexistsR with x; apply lorR1; reflexivity.
	+ destruct H as [[x]]; apply lexistsR with x; apply lorR2; reflexivity.
  Qed.

  Lemma lorexistsDR (f : T -> A) (P : A) :
     Exists a, (f a \\// P) |-- (Exists a, f a) \\// P.
  Proof.
  	apply lexistsL; intro x; apply lorL.
  	+ apply lorR1; apply lexistsR with x; reflexivity.
  	+ apply lorR2; reflexivity.
  Qed.

  Lemma lorexistsD (f : T -> A) (P : A) {H : Inhabited T} :
    (Exists a, f a) \\// P -|- Exists a, (f a \\// P).
  Proof.
    split; [apply lorexistsDL; apply H| apply lorexistsDR].
  Qed.


  Lemma landforallDL (f : T -> A) (P : A) :
    (Forall a, f a) //\\ P |-- Forall a, (f a //\\ P).
  Proof.
    apply lforallR; intro a; apply landR.
    + apply landL1; apply lforallL with a; reflexivity.
    + apply landL2; reflexivity.
  Qed.

  Lemma landforallDR {H: Inhabited T} (f : T -> A) (P : A) :
    Forall a, (f a //\\ P) |-- (Forall a, f a) //\\ P.
  Proof.
    apply landR.
    + apply lforallR; intro a; apply lforallL with a; apply landL1; reflexivity.
    + destruct H as [[a]]. apply lforallL with a; apply landL2; reflexivity.
  Qed.

  Lemma landforallD (f : T -> A) (P : A) {H : Inhabited T} :
    (Forall a, f a) //\\ P -|- Forall a, (f a //\\ P).
  Proof.
  	split; [apply landforallDL | apply landforallDR].
  Qed.


  Lemma lorforallDL (f : T -> A) (P : A) :
    (Forall a, f a) \\// P |-- Forall a, (f a \\// P).
  Proof.
  	apply lforallR; intro a; apply lorL.
  	+ apply lforallL with a; apply lorR1; reflexivity.
  	+ apply lorR2; reflexivity.
  Qed.

  Lemma limplTrue P : ltrue -->> P -|- P.
  Proof.
    split.
    + transitivity ((ltrue -->> P) //\\ ltrue).
      apply landR; [reflexivity | apply ltrueR].
      apply limplL; [apply ltrueR| apply landL1; reflexivity].
    + apply limplAdj; apply landL1; reflexivity.
  Qed.

  Lemma limplexistsE (P : T -> A) (Q : A) :
    (Exists x, P x) -->> Q -|- Forall x, (P x -->> Q).
  Proof.
    split.
	+ apply lforallR; intro x. apply limplAdj; apply limplL.
	  * apply lexistsR with x; reflexivity.
	  * apply landL1; reflexivity.
	+ apply limplAdj. rewrite landC, landexistsDL1.
	  apply lexistsL; intro x. rewrite landC, landforallDL.
	  apply lforallL with x. apply limplL.
	  * reflexivity.
	  * apply landL1. reflexivity.
  Qed.

  Lemma limplforallER (P : T -> A) (Q : A) :
    Exists x, (P x -->> Q) |-- (Forall x, P x) -->> Q.
  Proof.
  	apply lexistsL; intro x. apply limplAdj. apply limplL.
  	+ apply lforallL with x. reflexivity.
  	+ apply landL1. reflexivity.
  Qed.

  (* The following two lemmas have an explicit forall to help unification *)

  Lemma lforallR2 (P : A) (Q : T -> A) (H : P |-- lforall Q) :
  	forall x, P |-- Q x.
  Proof.
    intro x; rewrite H. apply lforallL with x; reflexivity.
  Qed.

  Lemma lexistsL2 (P : T -> A) (Q : A) (H : lexists P |-- Q) :
  	forall x, P x |-- Q.
  Proof.
    intro x; rewrite <- H. apply lexistsR with x; reflexivity.
  Qed.

  Lemma landtrueL : forall a, ltrue //\\ a -|- a.
  Proof.
    intros. split. eapply landL2. reflexivity. apply landR; eauto.
  Qed.

  Lemma landtrueR : forall a, a //\\ ltrue -|- a.
  Proof.
    intros. split. eapply landL1. reflexivity. apply landR; eauto.
  Qed.

  Lemma curry : forall a b c, (a //\\ b) -->> c -|- a -->> (b -->> c).
  Proof.
    clear - IL.
    intros.
    split.
    { eapply limplAdj.
      eapply limplAdj.
      rewrite landA.
      eapply landAdj.
      reflexivity. }
    { eapply limplAdj.
      rewrite <- landA.
      eapply landAdj.
      eapply landAdj. reflexivity. }
  Qed.

End ILogicFacts.

(* Prop is an intuitionistic logic *)

Global Instance ILogicOps_Prop : ILogicOps Prop := {|
  lentails P Q := (P : Prop) -> Q;
  ltrue        := True;
  lfalse       := False;
  limpl    P Q := P -> Q;
  land     P Q := P /\ Q;
  lor      P Q := P \/ Q;
  lforall  T F := forall x:T, F x;
  lexists  T F := exists x:T, F x
 |}.

Global Instance ILogic_Prop : ILogic Prop.
Proof.
  split; cbv; firstorder.
Qed.

(* Make the setoid system realize that these are the same things (in the
   direction that seems useful. *)
Instance: subrelation lentails Basics.impl.
Proof. reflexivity. Qed.

Instance: subrelation lequiv iff.
Proof. reflexivity. Qed.