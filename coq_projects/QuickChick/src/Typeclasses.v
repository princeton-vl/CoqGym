Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Classes DependentClasses Checker Show.

Require Import GenLow GenHigh Sets.
Import GenLow GenHigh.

(* TODO: Derive these *)
Instance arbST_eq {A} (a : A) : GenSuchThat A (fun x => x = a) :=
  {| arbitraryST := returnGen (Some a) |}.
Instance arbST_Correct {A} (a : A) 
  : SuchThatCorrect (fun x => x = a) (genST (fun x => x = a)).
Proof.
  constructor.
  simpl; rewrite semReturn.
  split; intros H. now firstorder.
  destruct H as [x [Heq H]]. subst. inversion H. subst.
  split; eauto.
Defined.

Instance arbST_eq' {A} (a : A) : GenSuchThat A (fun x => a = x) :=
  {| arbitraryST := returnGen (Some a) |}.
Instance arbST_Correct' {A} (a : A) 
  : SuchThatCorrect (fun x => a = x ) (genST (fun x => a = x)).
Proof.
  constructor.
  simpl; rewrite semReturn.
  split; intros H. now firstorder.
  destruct H as [x [Heq H]]. subst. inversion H. subst.
  split; eauto.
Defined.

(* Typeclass instances that derive checkable from dependent generators *)
(* Obvious TODO: Shrink *)

(* Is there another way of getting around the typeclass system? *)
Axiom ignore_generator_proofs : False.
Ltac ignore_gen_proofs := exfalso; apply ignore_generator_proofs.

Global Instance testSuchThat {A : Type} {pre : A -> Prop} {prop : A -> Type}
       `{Show A} `{GenSuchThat A (fun x => pre x)}
       `{forall (x : A), Checkable (prop x)} :
  Checkable (forall x, pre x -> prop x).
Proof.
refine
  {| checker f := forAllMaybe (genST (fun x => pre x))
                              (fun x => checker (f x _)) |}.
  ignore_gen_proofs.
Defined.

Global Instance testSuchThat2
       {A B : Type} {pre : A -> B -> Prop} {prop : A -> B -> Type}
       `{Show A} `{Show B} 
       `{GenSuchThat (A * B) (fun x => let (a,b) := x in pre a b)}
       `{forall (a : A) (b : B), Checkable (prop a b)} :
  Checkable (forall a b , pre a b -> prop a b).
Proof.
refine
  {| checker f := forAllMaybe (genST (fun x : A * B => let (a,b) := x in pre a b))
                              (fun x =>
                                 let (a,b) := x in
                                 checker (f a b _)) |}.
ignore_gen_proofs.
Defined.


(*
Definition t := forall x, x = 17 -> x = 17.
Instance ct : Checkable t.
  eapply testSuchThat; eauto.
  Unshelve.
  
  QuickChck t.

  (fun mx => match mx with
                                    | 
                              (fun mx H => 
                                 (* Leo: Is there a better way to do this? *)
                                 let mx' := mx in 
                                 let Heq := erefl mx' : mx' = mx in
                                 match mx as mx'' return (mx' = mx'' -> Checker) with 
                                 | Some x => fun _ => checker (f x _)
                                 | None => fun _ => checker tt
                                 end Heq) |}.
Proof.
  (* Annoying *)
  assert (Eq : mx = mx') by auto.
  rewrite -Eq in e.
  clear Heq Eq mx'.
  (* End annoying *)
  destruct H1. subst.
  (* Very annoying *)
  assert (Ha : (isSome :&: (semGen (genST [eta pre]))) (Some x)).
  { split; eauto. }
  apply STCorrect in Ha. destruct Ha as [y [Hin Heq]].
  inversion Heq. subst. eassumption.
Defined.     

Global Instance testSuchThat2_1 {A B : Type} {pre : A -> B -> Prop} {prop : A -> B -> Type}
       `{Show A} `{Show B} `{Arbitrary B}
       `{forall (b : B), GenSuchThat A (fun x => pre x b)}
       `{forall (b : B), SuchThatCorrect (fun x => pre x b) (genST (fun x => pre x b))}
       `{forall (a : A) (b : B), Checkable (prop a b)} :
  Checkable (forall a b , pre a b -> prop a b) :=
  {| checker f := 
       forAllShrink arbitrary shrink (fun b => 
         forAllProof (genST (fun x => pre x b)) 
                     (fun mx H => 
                        (* Leo: Is there a better way to do this? *)
                        let mx' := mx in 
                        let Heq := erefl mx' : mx' = mx in
                        match mx as mx'' return (mx' = mx'' -> Checker) with 
                        | Some x => fun _ => checker (f x b _)
                        | None => fun _ => checker tt
                        end Heq)
                                     ) |}.
Proof.
  (* Annoying *)
  assert (Eq : mx = mx') by auto.
  rewrite -Eq in e.
  clear Heq Eq mx'.
  (* End annoying *)
  destruct (H5 b).
  (* Very annoying *)
  subst.
  assert (Ha : (isSome :&: semGen (genST pre^~ b)) (Some x)).
  { split; eauto. }
  apply STCorrect in Ha. destruct Ha as [y [Hin Heq]].
  inversion Heq. subst. eassumption.
Defined.     

Global Instance testSuchThat2_2 {A B : Type} {pre : A -> B -> Prop} {prop : A -> B -> Type}
       `{Show A} `{Show B} `{Arbitrary A}
       `{forall (a : A), GenSuchThat B (fun x => pre a x)}
       `{forall (a : A), SuchThatCorrect (fun x => pre a x) (genST (fun x => pre a x))}
       `{forall (a : A) (b : B), Checkable (prop a b)} :
  Checkable (forall a b , pre a b -> prop a b) :=
  {| checker f := 
       forAllShrink arbitrary shrink (fun a => 
         forAllProof (genST (fun x => pre a x)) 
                     (fun mx H =>  
                        (* Leo: Is there a better way to do this? *)
                        let mx' := mx in 
                        let Heq := erefl mx' : mx' = mx in
                        match mx as mx'' return (mx' = mx'' -> Checker) with 
                        | Datatypes.Some x => fun _ => checker (f a x _)
                        | Datatypes.None => fun _ => checker tt
                        end Heq)
                                     ) |}.
Proof.
  (* Annoying *)
  assert (Eq : mx = mx') by auto.
  rewrite -Eq in e.
  clear Heq Eq mx'.
  (* End annoying *)
  destruct (H5 a).
  (* Very annoying *)
  subst.
  assert (Ha : (isSome :&: semGen (genST [eta pre a])) (Some x)).
  { split; eauto. }
  apply STCorrect in Ha. destruct Ha as [y [Hin Heq]].
  inversion Heq. subst. eassumption.
Defined.     

Global Instance testSuchThat_swap {A B C : Type} {pre : A -> B -> Prop} 
       {prop : A -> B -> C -> Type}
       `{Checkable (forall a b, pre a b -> forall c, prop a b c)} :
  Checkable (forall a b c, pre a b -> prop a b c) :=
  {| checker f := @checker (forall a b, pre a b -> forall c, prop a b c) _ _ |}. 
Proof. intros; eauto. Defined.

Global Instance GenSuchThatConj {A B : Type} (P : A -> Prop) (Q : B -> Prop)
       `{GenSuchThat A (fun x => P x)}
       `{GenSuchThat B (fun x => Q x)}
       : GenSuchThat (A * B) (fun xy => let (x,y) := xy in P x /\ Q y) :=
  {| arbitraryST := 
       bindGen (genST (fun x => P x)) (fun ma =>
       bindGen (genST (fun x => Q x)) (fun mb =>
       match ma, mb with 
       | Some a, Some b => returnGen (Some (a,b))
       | _, _ => returnGen None
       end)) |}.



(*
Global Instance GenSuchThatConjCorrect {A B : Type} (P : A -> Prop) (Q : B -> Prop)
       `{GA: GenSizedSuchThat A (fun x => P x)}
       `{GB: GenSizedSuchThat B (fun x => Q x)}
       `{SizedSuchThatCorrectSuchThatSizedCorrect A (fun x => P x) (@arbitraryST _ _ GA)}
       `{SuchThatSizeCorrect B (fun x => Q x) (@arbitraryST _ _ GB)} 
  : SuchThatCorrect (fun xy : A * B => let (x,y) := xy in P x /\ Q y) 
                    (@arbitraryST _ (fun xy => let (x,y) := xy : A * B in P x /\ Q y) 
                                  (@GenSuchThatConj A B P Q GA GB)) :=
  {| STComplete := _ ;
     STSound    := _ |}.
Proof.
- simpl. rewrite semBind
  *)


*)